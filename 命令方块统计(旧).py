#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Minecraft 基岩版地图「命令方块」统计工具  ·  单文件 / 纯标准库
================================================================

功能概览
--------
1. 解析存档：支持 .mcworld / .zip / 直接上传 LevelDB 文件（.ldb / .log）
2. 读取数据：纯 Python 实现 LevelDB（SST 表 + WAL 日志）、snappy/zlib 解压块、
   基岩版小端 NBT，从方块实体中提取 CommandBlock（命令方块）
3. 统计维度：总数、维度分布、模式分布、条件/红石/自动执行、延迟、指令首词排行、
   重复命令、命令长度、坐标范围、风险提示、其它方块实体概览等
4. 导出 CSV：明细表、汇总表、排行榜、方块实体表（UTF-8 BOM，Excel 直接打开）
5. 浏览器交互：内置 http.server，手机 / 电脑打开网址即可上传文件、查看进度、
   浏览统计结果并下载 CSV；同时保留纯命令行模式

命令行示例
----------
    python mc_command_block_stats.py                       # 启动网页界面（默认 0.0.0.0:8765）
    python mc_command_block_stats.py --port 9000
    python mc_command_block_stats.py -f world.mcworld -o out/   # 纯命令行导出 CSV
    python mc_command_block_stats.py --selftest            # 内置自检（自造合成存档并校验解析结果）

依赖：仅 Python 3.8+ 标准库（无第三方包、无需联网）
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import os
import re
import socket
import struct
import sys
import threading
import time
import uuid
import zipfile
import zlib
from collections import Counter, OrderedDict
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

APP_NAME = "基岩版命令方块统计"
APP_EN = "mc-command-block-stats"
VERSION = "2.0.0"

# ---------------------------------------------------------------------------
# 常量表
# ---------------------------------------------------------------------------

DIM_NAMES = {0: "主世界", 1: "下界", 2: "末地"}

# LPCommandMode 的语义标签按常见 NBT 约定推断，导出时同时保留原始数值
MODE_NAMES = {0: "脉冲 Impulse", 1: "循环 Repeat", 2: "连锁 Chain"}

# 这些键型的 key 结构为 [type][chunkX int32][chunkZ int32][dimension int32]...
CHUNK_KEY_TYPES = {
    0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
    0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x76, 0x77,
}

# 其它方块实体（用于上下文概览，命中即计数）
KNOWN_ENTITY_IDS = {
    "chest", "trappedchest", "barrel", "shulkerbox", "enderchest", "furnace",
    "blastfurnace", "smoker", "brewingstand", "enchanttable", "beacon", "sign",
    "hangingsign", "mobspawner", "jukebox", "lectern", "campfire", "flowerpot",
    "skull", "banner", "beehive", "beenest", "cauldron", "bed", "pistonarm",
    "movingblock", "netherreactor", "structureblock", "structure_void",
    "daylightdetector", "comparator", "dispenser", "dropper", "hopper",
    "noteblock", "conduit", "endportal", "endgateway", "bell", "sculksensor",
    "sculkshrieker", "calibratedsculksensor", "chiseledbookshelf",
    "decoratedpot", "crafter", "vault", "trialspawner", "creakingheart",
    "frame", "glowframe", "mobspawner", "skullblock", "piston",
}

_ENTITY_TOKENS = [
    b"Chest", b"Barrel", b"ShulkerBox", b"EnderChest", b"Furnace", b"Smoker",
    b"BrewingStand", b"EnchantTable", b"Beacon", b"Sign", b"MobSpawner",
    b"Jukebox", b"Lectern", b"Campfire", b"FlowerPot", b"Skull", b"Banner",
    b"Beehive", b"BeeNest", b"Cauldron", b"Bed", b"PistonArm", b"MovingBlock",
    b"NetherReactor", b"StructureBlock", b"Comparator", b"Dispenser",
    b"Dropper", b"Hopper", b"NoteBlock", b"Conduit", b"EndPortal",
    b"EndGateway", b"Bell", b"SculkSensor", b"SculkShrieker",
    b"ChiseledBookshelf", b"DecoratedPot", b"Crafter", b"Vault",
    b"TrialSpawner", b"BlastFurnace", b"DaylightDetector", b"CreakingHeart",
]
# 单次正则扫描完成全部候选过滤（比逐个 in 判断快得多）
_ENTITY_PRE = re.compile(b"|".join(_ENTITY_TOKENS))

KNOWN_COMMANDS = {
    "execute", "tp", "teleport", "setblock", "fill", "clone", "give", "summon",
    "kill", "say", "tell", "tellraw", "titleraw", "title", "scoreboard", "tag",
    "function", "particle", "playsound", "effect", "gamerule", "setworldspawn",
    "setspawnpoint", "spawnpoint", "time", "weather", "gamemode", "difficulty",
    "clear", "replaceitem", "structure", "camerashake", "fog", "dialogue",
    "input", "testfor", "testforblock", "testforblocks", "tickingarea", "help",
    "list", "me", "msg", "w", "xp", "damage", "loot", "ride", "schedule",
    "spreadplayers", "stopsound", "music", "event", "moveto", "playanimation",
    "enchant", "xp", "immutableworld", "reload", "scoreboardplayers", "new",
    "blockdata", "connect", "deop", "op", "change", "recipe", "whitelist",
}


# ---------------------------------------------------------------------------
# 基础工具：varint / 定长整数
# ---------------------------------------------------------------------------

class NbtError(Exception):
    """NBT / 二进制结构解析失败"""


def read_uvarint(buf: bytes, pos: int):
    """LEB128 无符号 varint（LevelDB 与基岩网络 NBT 共用）"""
    result = 0
    shift = 0
    n = len(buf)
    while True:
        if pos >= n:
            raise NbtError("varint eof")
        b = buf[pos]
        pos += 1
        result |= (b & 0x7F) << shift
        if b < 0x80:
            return result, pos
        shift += 7
        if shift > 70:
            raise NbtError("varint overflow")


def encode_uvarint(value: int) -> bytes:
    out = bytearray()
    while True:
        b = value & 0x7F
        value >>= 7
        if value:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def _u16(buf: bytes, pos: int):
    if pos + 2 > len(buf):
        raise NbtError("eof")
    return buf[pos] | (buf[pos + 1] << 8), pos + 2


def _u32(buf: bytes, pos: int):
    if pos + 4 > len(buf):
        raise NbtError("eof")
    return int.from_bytes(buf[pos:pos + 4], "little"), pos + 4


def _zigzag(v: int) -> int:
    return (v >> 1) ^ -(v & 1)


# ---------------------------------------------------------------------------
# Snappy 解压（纯 Python 实现，LevelDB 数据块常用）
# ---------------------------------------------------------------------------

def snappy_uncompress(data: bytes) -> bytes:
    """解压 snappy 数据（Literal / Copy1 / Copy2 / Copy4 四种 tag）"""
    pos = 0
    expected, pos = read_uvarint(data, pos)
    out = bytearray()
    n = len(data)
    while pos < n:
        tag = data[pos]
        pos += 1
        kind = tag & 0x03
        if kind == 0:  # literal
            ln = tag >> 2
            if ln < 60:
                ln += 1
            else:
                extra = ln - 59
                if pos + extra > n:
                    raise NbtError("snappy literal eof")
                ln = int.from_bytes(data[pos:pos + extra], "little") + 1
                pos += extra
            if pos + ln > n:
                raise NbtError("snappy literal overflow")
            out += data[pos:pos + ln]
            pos += ln
            continue
        if kind == 1:
            ln = ((tag >> 2) & 0x07) + 4
            if pos + 1 > n:
                raise NbtError("snappy copy eof")
            offset = ((tag >> 5) << 8) | data[pos]
            pos += 1
        elif kind == 2:
            ln = (tag >> 2) + 1
            if pos + 2 > n:
                raise NbtError("snappy copy eof")
            offset = data[pos] | (data[pos + 1] << 8)
            pos += 2
        else:
            ln = (tag >> 2) + 1
            if pos + 4 > n:
                raise NbtError("snappy copy eof")
            offset = int.from_bytes(data[pos:pos + 4], "little")
            pos += 4
        if offset <= 0 or offset > len(out):
            raise NbtError("snappy bad offset")
        start = len(out) - offset
        for i in range(ln):
            out.append(out[start + i])
    if expected and len(out) != expected:
        # 长度不符时仍返回已解出的内容，由调用方按 NBT 解析结果判断可用性
        pass
    return bytes(out)


def snappy_compress_literal(data: bytes) -> bytes:
    """仅供自检使用：生成「全 literal」的合法 snappy 流"""
    out = bytearray(encode_uvarint(len(data)))
    i = 0
    while i < len(data):
        chunk = data[i:i + 60]
        out.append(((len(chunk) - 1) << 2) | 0)
        out += chunk
        i += len(chunk)
    return bytes(out)


# ---------------------------------------------------------------------------
# LevelDB：块 / SST 表 / WAL 日志
# ---------------------------------------------------------------------------

# 压缩类型：0 无 / 1 snappy / 2 zlib / 3 gzip / 4 raw-deflate（基岩版各实现混用）
BLOCK_NONE, BLOCK_SNAPPY, BLOCK_ZLIB, BLOCK_GZIP, BLOCK_DEFLATE = 0, 1, 2, 3, 4
BLOCK_LZ4 = 5
_SST_MAGIC = b"\x57\xfb\x80\x8b\x24\x75\x47\xdb"
LOG_BLOCK_SIZE = 32768


def _decompress_block(body: bytes, ctype: int) -> bytes:
    if ctype == BLOCK_NONE:
        return body
    if ctype == BLOCK_SNAPPY:
        return snappy_uncompress(body)
    if ctype == BLOCK_ZLIB:
        return zlib.decompress(body)
    if ctype == BLOCK_GZIP:
        return zlib.decompress(body, 31)
    if ctype == BLOCK_DEFLATE:
        return zlib.decompress(body, -15)
    raise NbtError("不支持的压缩类型 %d" % ctype)


_DECOMPRESSORS = (
    lambda b: b,
    snappy_uncompress,
    zlib.decompress,
    lambda b: zlib.decompress(b, 31),
    lambda b: zlib.decompress(b, -15),
)


def _decompress_any(body: bytes, ctype=None) -> bytes:
    """按声明的压缩类型解压；类型未知或失败时逐个回退尝试全部已知算法。"""
    if ctype is not None and 0 <= ctype < len(_DECOMPRESSORS):
        try:
            out = _DECOMPRESSORS[ctype](body)
            if ctype != BLOCK_NONE or out:
                return out
        except Exception:
            pass
    for fn in _DECOMPRESSORS:
        try:
            out = fn(body)
        except Exception:
            continue
        if out:
            return out
    raise NbtError("无法解压数据块")


def _block_looks_valid(payload: bytes) -> bool:
    """块尾部应有合法的 restart 数组，用于校验块边界与压缩方式是否选对。"""
    if len(payload) < 8:
        return False
    n = int.from_bytes(payload[-4:], "little")
    if n < 1 or 4 + n * 4 > len(payload):
        return False
    head = payload[len(payload) - 4 - n * 4:len(payload) - n * 4]
    return int.from_bytes(head, "little") < len(payload)


def _find_block_min(data: bytes, offset: int, limit=None):
    """从 offset 起扫描出最短的合法数据块，返回 (解压后的块, 块结束位置)。"""
    hi = min(len(data) - 5, limit if limit is not None else len(data) - 5)
    for end in range(offset + 5, hi + 1):
        ctype = data[end - 5]
        if ctype > BLOCK_LZ4:
            continue
        body = data[offset:end - 5]
        try:
            out = _decompress_any(body, ctype)
        except Exception:
            continue
        if not _block_looks_valid(out):
            continue
        if ctype == BLOCK_NONE:
            # 未压缩块必须真的能解析出条目，避免把任意前缀误判成块
            try:
                next(iter_block_entries(out))
            except Exception:
                continue
        return out, end
    raise NbtError("未找到有效数据块")


def read_block_payload(data: bytes, offset: int, size: int) -> bytes:
    """读取一个 LevelDB 数据块（内部块或索引块）。

    BlockHandle 的 size 语义在不同写入端并不统一：标准 LevelDB 含尾部
    5 字节 [压缩类型 1B][CRC32 4B]，而部分实现（含基岩版常见存档）不含。
    因此两种长度都尝试，并用 restart 数组校验，必要时再回退到扫描。
    """
    if offset < 0 or size < 0 or offset > len(data):
        raise NbtError("block out of range")
    last_err = None
    for extra in (0, 5):
        end = offset + size + extra
        if end > len(data) or end - 5 < offset:
            continue
        body = data[offset:end - 5]
        try:
            out = _decompress_any(body, data[end - 5])
        except Exception as exc:
            last_err = exc
            continue
        if _block_looks_valid(out):
            return out
        last_err = NbtError("块结构校验失败")
    try:
        span = max(4096, size * 4 + 64)
        return _find_block_min(data, offset, offset + span)[0]
    except Exception as exc:
        raise NbtError("读取数据块失败：%s" % (last_err or exc))


def read_leveldb_block(data: bytes, offset: int, size: int) -> bytes:
    """兼容旧调用名。"""
    return read_block_payload(data, offset, size)


def iter_block_entries(block: bytes):
    """遍历一个 LevelDB 数据块内的 (key, value) 对"""
    if len(block) < 4:
        return
    num_restarts = int.from_bytes(block[-4:], "little")
    if num_restarts <= 0 or num_restarts * 4 + 4 > len(block):
        num_restarts = 0
    limit = len(block) - 4 - num_restarts * 4
    pos = 0
    last_key = b""
    while pos < limit:
        try:
            shared, pos = read_uvarint(block, pos)
            unshared, pos = read_uvarint(block, pos)
            vlen, pos = read_uvarint(block, pos)
        except NbtError:
            return
        if shared > len(last_key) or pos + unshared + vlen > len(block):
            return
        key = last_key[:shared] + block[pos:pos + unshared]
        pos += unshared
        value = block[pos:pos + vlen]
        pos += vlen
        last_key = key
        yield key, value


def read_sst_entries(data: bytes):
    """读取 .ldb（SST）文件内的全部 key/value。

    通过文件尾部 48 字节 footer 定位 index 块，再由 index 枚举数据块。
    """
    if len(data) < 48 or data[-8:] != _SST_MAGIC:
        raise NbtError("不是合法的 LevelDB 表文件")
    footer = data[-48:-8]
    pos = 0
    try:
        _meta_off, pos = read_uvarint(footer, pos)
        _meta_size, pos = read_uvarint(footer, pos)
        idx_off, pos = read_uvarint(footer, pos)
        idx_size, pos = read_uvarint(footer, pos)
    except NbtError:
        raise NbtError("footer 结构异常")
    entries = []
    index_block = None
    try:
        index_block = read_block_payload(data, idx_off, idx_size)
    except Exception:
        index_block = None
    if index_block is not None:
        for _key, value in iter_block_entries(index_block):
            try:
                off, p = read_uvarint(value, 0)
                size, _p = read_uvarint(value, p)
            except NbtError:
                continue
            try:
                block = read_block_payload(data, off, size)
            except Exception:
                continue
            entries.extend(iter_block_entries(block))
    if not entries:
        # 索引块不可用时，按“连续块”布局顺序扫描整张表
        entries = _scan_sst_entries(data)
    return entries


def _scan_sst_entries(data: bytes):
    """兜底：索引块损坏或无索引时，顺序扫描表内所有数据块。"""
    out = []
    pos = 0
    limit = len(data) - 8
    guard = 0
    while pos + 9 < limit and guard < 200000:
        guard += 1
        try:
            payload, end = _find_block_min(data, pos, min(limit, pos + 16 * 1024 * 1024))
        except Exception:
            break
        if end <= pos:
            break
        out.extend(iter_block_entries(payload))
        pos = end
    return out


def iter_log_records(data: bytes):
    """解析 LevelDB WAL(.log) 记录，处理跨块分片(FSM/LSM)"""
    pos = 0
    n = len(data)
    pending = bytearray()
    while pos + 7 <= n:
        blk = pos % LOG_BLOCK_SIZE
        if blk + 7 > LOG_BLOCK_SIZE:
            pos += LOG_BLOCK_SIZE - blk
            continue
        length = int.from_bytes(data[pos + 4:pos + 6], "little")
        rtype = data[pos + 6]
        pos += 7
        if length == 0 and rtype == 0:
            pos = (pos // LOG_BLOCK_SIZE + 1) * LOG_BLOCK_SIZE
            continue
        if pos + length > n:
            break
        chunk = data[pos:pos + length]
        pos += length
        if rtype == 1:  # FULL
            pending = bytearray()
            yield chunk
        elif rtype == 2:  # FIRST
            pending = bytearray(chunk)
        elif rtype == 3:  # MIDDLE
            pending += chunk
        elif rtype == 4:  # LAST
            pending += chunk
            yield bytes(pending)
            pending = bytearray()


def _parse_write_batch(payload: bytes, base: int):
    """从 base 起解析 varint32 klen/key/varint32 vlen/value，返回 (条目, 是否完整消费)"""
    pos = base
    n = len(payload)
    out = []
    while pos < n:
        try:
            klen, pos = read_uvarint(payload, pos)
        except NbtError:
            return out, False
        if klen <= 0 or pos + klen > n:
            return out, False
        key = payload[pos:pos + klen]
        pos += klen
        try:
            vlen, pos = read_uvarint(payload, pos)
        except NbtError:
            return out, False
        if vlen < 0 or pos + vlen > n:
            return out, False
        value = payload[pos:pos + vlen]
        pos += vlen
        out.append((key, value))
    return out, True


def iter_write_batch(payload: bytes):
    """解析 WAL 记录内的 key/value 序列。

    标准 LevelDB 写批次前面还有 [序列号 8B][条数 4B] 头部，不同实现可能省略，
    这里两种布局都尝试，取能够完整消费整段数据的那个。
    """
    if len(payload) >= 12:
        items, ok = _parse_write_batch(payload, 12)
        if ok and items:
            return iter(items)
    items, _ok = _parse_write_batch(payload, 0)
    return iter(items)


# ---------------------------------------------------------------------------
# 基岩版 NBT 解析（磁盘小端格式优先，自动兼容 varint 变体）
# ---------------------------------------------------------------------------

MODE_LE = {"str": "le16", "int": "le32"}   # 基岩磁盘 NBT（字符串 2 字节长度、整数定长小端）
MODE_VARINT = {"str": "varint", "int": "zigzag"}  # 网络/变体 NBT

TAG_END, TAG_BYTE, TAG_SHORT, TAG_INT, TAG_LONG = 0, 1, 2, 3, 4
TAG_FLOAT, TAG_DOUBLE, TAG_BYTE_ARRAY, TAG_STRING = 5, 6, 7, 8
TAG_LIST, TAG_COMPOUND, TAG_INT_ARRAY, TAG_LONG_ARRAY = 9, 10, 11, 12

_MAX_STR = 1 << 20
_MAX_LIST = 200000
_MAX_ARRAY = 200000


def _nbt_name(buf: bytes, pos: int, st: str):
    if st == "le16":
        ln, pos = _u16(buf, pos)
    else:
        ln, pos = read_uvarint(buf, pos)
    if ln > 512 or pos + ln > len(buf):
        raise NbtError("bad name")
    return buf[pos:pos + ln].decode("utf-8", "replace"), pos + ln


def _nbt_value(buf: bytes, pos: int, tag: int, st: str, it: str, depth: int):
    if depth > 24:
        raise NbtError("depth limit")
    if tag == TAG_BYTE:
        if pos + 1 > len(buf):
            raise NbtError("eof")
        v = buf[pos]
        return (v - 256 if v >= 128 else v), pos + 1
    if tag == TAG_SHORT:
        if pos + 2 > len(buf):
            raise NbtError("eof")
        return int.from_bytes(buf[pos:pos + 2], "little", signed=True), pos + 2
    if tag == TAG_INT:
        if it == "le32":
            if pos + 4 > len(buf):
                raise NbtError("eof")
            return int.from_bytes(buf[pos:pos + 4], "little", signed=True), pos + 4
        v, pos = read_uvarint(buf, pos)
        return _zigzag(v), pos
    if tag == TAG_LONG:
        if it == "le32":
            if pos + 8 > len(buf):
                raise NbtError("eof")
            return int.from_bytes(buf[pos:pos + 8], "little", signed=True), pos + 8
        v, pos = read_uvarint(buf, pos)
        return _zigzag(v), pos
    if tag == TAG_FLOAT:
        if pos + 4 > len(buf):
            raise NbtError("eof")
        return struct.unpack("<f", buf[pos:pos + 4])[0], pos + 4
    if tag == TAG_DOUBLE:
        if pos + 8 > len(buf):
            raise NbtError("eof")
        return struct.unpack("<d", buf[pos:pos + 8])[0], pos + 8
    if tag == TAG_BYTE_ARRAY:
        cnt, pos = (_u32(buf, pos) if st == "le16" else read_uvarint(buf, pos))
        if cnt < 0 or pos + cnt > len(buf):
            raise NbtError("byte array")
        return "<%d 字节>" % cnt, pos + cnt
    if tag == TAG_STRING:
        if st == "le16":
            ln, pos = _u16(buf, pos)
        else:
            ln, pos = read_uvarint(buf, pos)
        if ln > _MAX_STR or pos + ln > len(buf):
            raise NbtError("string")
        return buf[pos:pos + ln].decode("utf-8", "replace"), pos + ln
    if tag == TAG_LIST:
        if pos + 1 > len(buf):
            raise NbtError("eof")
        et = buf[pos]
        pos += 1
        cnt, pos = (_u32(buf, pos) if st == "le16" else read_uvarint(buf, pos))
        if cnt > _MAX_LIST:
            raise NbtError("list too long")
        out = []
        for _ in range(cnt):
            v, pos = _nbt_value(buf, pos, et, st, it, depth + 1)
            out.append(v)
        return out, pos
    if tag == TAG_COMPOUND:
        out = {}
        while True:
            if pos >= len(buf):
                raise NbtError("eof")
            t = buf[pos]
            pos += 1
            if t == TAG_END:
                return out, pos
            name, pos = _nbt_name(buf, pos, st)
            v, pos = _nbt_value(buf, pos, t, st, it, depth + 1)
            out[name] = v
    if tag == TAG_INT_ARRAY:
        cnt, pos = (_u32(buf, pos) if st == "le16" else read_uvarint(buf, pos))
        if it == "le32":
            if cnt > _MAX_ARRAY or pos + cnt * 4 > len(buf):
                raise NbtError("int array")
            return [int.from_bytes(buf[pos + i * 4:pos + i * 4 + 4], "little", signed=True)
                    for i in range(cnt)], pos + cnt * 4
        vals = []
        if cnt > _MAX_ARRAY:
            raise NbtError("int array")
        for _ in range(cnt):
            v, pos = read_uvarint(buf, pos)
            vals.append(_zigzag(v))
        return vals, pos
    if tag == TAG_LONG_ARRAY:
        cnt, pos = (_u32(buf, pos) if st == "le16" else read_uvarint(buf, pos))
        if it == "le32":
            if cnt > _MAX_ARRAY or pos + cnt * 8 > len(buf):
                raise NbtError("long array")
            return [int.from_bytes(buf[pos + i * 8:pos + i * 8 + 8], "little", signed=True)
                    for i in range(cnt)], pos + cnt * 8
        vals = []
        for _ in range(cnt):
            v, pos = read_uvarint(buf, pos)
            vals.append(_zigzag(v))
        return vals, pos
    raise NbtError("tag %d" % tag)


def parse_named_compound(buf: bytes, pos: int, modes) -> tuple:
    """从 pos 处解析一个「带名字的 Compound」（NBT 数据流根节点）"""
    if pos >= len(buf) or buf[pos] != TAG_COMPOUND:
        raise NbtError("not compound")
    p = pos + 1
    _name, p = _nbt_name(buf, p, modes["str"])
    value, p = _nbt_value(buf, p, TAG_COMPOUND, modes["str"], modes["int"], 1)
    return value, p


def parse_level_dat(data: bytes):
    """解析 level.dat（8 字节头 + 小端 NBT），提取世界基础信息"""
    info = {}
    for off in (8, 0):
        if off >= len(data):
            continue
        try:
            root, _ = parse_named_compound(data, off, MODE_LE)
        except NbtError:
            try:
                root, _ = parse_named_compound(data, off, MODE_VARINT)
            except NbtError:
                continue
        if not isinstance(root, dict):
            continue
        keys = ("LevelName", "RandomSeed", "StorageVersion", "GameType",
                "Difficulty", "LastPlayed", "SpawnX", "SpawnY", "SpawnZ",
                "FlatWorldLayers", "Generator", "NetherScale", "commandsEnabled")
        for k in keys:
            if k in root:
                info[k] = root[k]
        if info:
            return info, root
    return {}, {}


def scan_compounds(value: bytes, max_attempts: int = 400000, max_results: int = 4096):
    """在任意二进制块中扫描出所有「像 NBT 方块实体」的 Compound。

    基岩版不同版本把方块实体放在不同位置（子区块载荷内 / 独立 block-entity 记录），
    这里不依赖具体版式：从每个 0x0A(Compound) 字节尝试解析，成功且带 id 字段即采纳。
    """
    results = []
    n = len(value)
    i = 0
    attempts = 0
    while i < n and attempts < max_attempts and len(results) < max_results:
        if value[i] != TAG_COMPOUND:
            i += 1
            continue
        attempts += 1
        ok = False
        for modes in (MODE_LE, MODE_VARINT):
            try:
                comp, end = parse_named_compound(value, i, modes)
            except Exception:
                continue
            if isinstance(comp, dict) and isinstance(comp.get("id"), str):
                results.append((comp, i, end))
                i = end if end > i else i + 1
                ok = True
                break
        if not ok:
            i += 1
    return results




# ---------------------------------------------------------------------------
# 存档加载：.mcworld / .zip / 裸 LevelDB 文件
# ---------------------------------------------------------------------------

DB_NAME_RE = re.compile(r"^(\d+)\.(ldb|sst|log)$", re.I)


class Progress:
    """把进度回调包装成安全调用的形式"""

    def __init__(self, cb=None):
        self.cb = cb

    def __call__(self, percent, stage, message=""):
        if self.cb:
            try:
                self.cb(int(percent), stage, message)
            except Exception:
                pass


def _looks_like_sst(data: bytes) -> bool:
    return len(data) > 48 and data[-8:] == _SST_MAGIC


def load_world_inputs(files, progress=None):
    """输入 (文件名, 原始字节) 列表 -> 待解析的 db 文件 / level.dat / 提示信息"""
    p = progress or Progress()
    db_files = []
    archive_names = []
    level_dat = None
    level_name_txt = None
    warnings = []
    total = len(files) or 1
    for idx, (name, data) in enumerate(files):
        base = os.path.basename(name or "")
        p(5 + int(20 * idx / total), "读取文件", "正在解包 %s" % base)
        if base.lower().endswith((".zip", ".mcworld")) or data[:2] == b"PK":
            try:
                zf = zipfile.ZipFile(io.BytesIO(data))
            except Exception as exc:
                warnings.append("%s 不是有效压缩包：%s" % (base, exc))
                continue
            for info in zf.infolist():
                entry = info.filename.replace("\\", "/")
                ebase = entry.rsplit("/", 1)[-1]
                if info.is_dir():
                    continue
                try:
                    if info.file_size > 512 * 1024 * 1024:
                        warnings.append("%s 内 %s 过大，已跳过" % (base, entry))
                        continue
                    if DB_NAME_RE.match(ebase):
                        db_files.append((entry, zf.read(info)))
                        archive_names.append(entry)
                    elif ebase.lower() == "level.dat":
                        level_dat = zf.read(info)
                        archive_names.append(entry)
                    elif ebase.lower() == "levelname.txt":
                        level_name_txt = zf.read(info).decode("utf-8", "replace").strip()
                except Exception as exc:
                    warnings.append("读取 %s 失败：%s" % (entry, exc))
        elif DB_NAME_RE.match(base) or base.lower().endswith((".ldb", ".sst", ".log")):
            db_files.append((base, data))
        elif base.lower() == "level.dat":
            level_dat = data
        elif base.lower() == "levelname.txt":
            level_name_txt = data.decode("utf-8", "replace").strip()
        elif data[:8] and _looks_like_sst(data):
            db_files.append((base or "unnamed.ldb", data))
        else:
            warnings.append("%s 无法识别为存档 / LevelDB 文件，已忽略" % (base or "未命名文件"))
    if not db_files:
        warnings.append("没有找到 LevelDB 数据文件（应为 .mcworld/.zip 存档，或 db/ 下的 .ldb、.log 文件）")
    db_files.sort(key=lambda x: x[0])
    return {
        "db_files": db_files,
        "level_dat": level_dat,
        "levelname_txt": level_name_txt,
        "archive_names": archive_names,
        "warnings": warnings,
    }


def collect_records(db_files, warnings, progress=None):
    """把所有 .ldb/.log 的 key/value 合并为一张「最新写入生效」的表"""
    p = progress or Progress()
    records = {}
    total = len(db_files) or 1
    parsed = 0
    for idx, (name, data) in enumerate(db_files):
        base = os.path.basename(name)
        p(25 + int(35 * idx / total), "解析 LevelDB", "解析 %s" % base)
        m = DB_NAME_RE.match(base)
        num = int(m.group(1)) if m else 0
        is_log = base.lower().endswith(".log")
        # 同一编号下 .log 比 .ldb 新；编号越大越新 -> 优先级越高
        prio = num * 10 + (5 if is_log else 0)
        pairs = []
        try:
            if is_log:
                for rec in iter_log_records(data):
                    pairs.extend(iter_write_batch(rec))
            else:
                pairs = read_sst_entries(data)
        except Exception as exc:
            warnings.append("%s 解析异常（已跳过部分数据）：%s" % (base, exc))
        parsed += 1
        for key, value in pairs:
            old = records.get(key)
            if old is None or prio >= old[0]:
                records[key] = (prio, value, base)
    return records, parsed


# 区块记录类型字节（0x2B Data3D / 0x2F SubChunkPrefix / 0x31 BlockEntity / 0x36 FinalizedState ...）
CHUNK_RECORD_TYPES = set(range(0x2B, 0x42)) | {0x76, 0x77, 0x7A}


def is_chunk_key(key: bytes) -> bool:
    """判断键是否为区块键（actorprefix / digp / Overworld 等文本键会被排除）"""
    if not key or len(key) < 9:
        return False
    x = int.from_bytes(key[0:4], "little", signed=True)
    z = int.from_bytes(key[4:8], "little", signed=True)
    return abs(x) < (1 << 23) and abs(z) < (1 << 23)


def decode_chunk_key(key: bytes):
    """解析区块键，返回 (维度, 区块X, 区块Z, 记录类型)。

    基岩版区块键为 [chunkX int32][chunkZ int32][dimension int32][类型字节]；
    当维度为 0（主世界）时，部分存档会省略维度字段，两种布局都在此兼容。
    """
    if not is_chunk_key(key):
        return (None, None, None, None)
    x = int.from_bytes(key[0:4], "little", signed=True)
    z = int.from_bytes(key[4:8], "little", signed=True)
    b = key[8]
    if len(key) >= 13 and b in (0, 1, 2) and key[9] == 0 and key[10] == 0 and key[11] == 0:
        rtype = key[12]
        if rtype in CHUNK_RECORD_TYPES or rtype >= 0x2B:
            return (b, x, z, rtype)
    return (0, x, z, b)


# ---------------------------------------------------------------------------
# 方块实体与命令方块提取
# ---------------------------------------------------------------------------

def _first(comp, names, kinds=(int, str)):
    for n in names:
        if n in comp and isinstance(comp[n], kinds) and not isinstance(comp[n], bool):
            return comp[n]
    return None


def _flag(comp, names):
    v = _first(comp, names, (int, bool))
    if v is None:
        return None
    return 1 if int(v) != 0 else 0


def make_command_block(comp, dim, chunk, source, prio):
    raw_cmd = _first(comp, ("Command",), (str,)) or ""
    cmd = raw_cmd[1:] if raw_cmd.startswith("/") else raw_cmd
    cmd_stripped = cmd.strip()
    base = ""
    if cmd_stripped:
        base = cmd_stripped.split(" ", 1)[0].lower().lstrip("/")
    mode_raw = _first(comp, ("LPCommandMode",), (int,))
    mode_label = "" if mode_raw is None else MODE_NAMES.get(mode_raw, "未知(%s)" % mode_raw)
    return {
        "dim": dim,
        "x": _first(comp, ("x", "X")),
        "y": _first(comp, ("y", "Y")),
        "z": _first(comp, ("z", "Z")),
        "chunk_x": chunk[0],
        "chunk_z": chunk[1],
        "mode_raw": mode_raw,
        "mode": mode_label,
        "conditional": _flag(comp, ("LPCondionalMode", "LPConditionalMode", "conditional")),
        "redstone": _flag(comp, ("LPRedstoneMode", "LPRedstoneMode", "needsRedstone")),
        "auto": _flag(comp, ("ExecuteOnFirstTick", "auto")),
        "tick_delay": _first(comp, ("TickDelay", "delay"), (int,)),
        "command": cmd_stripped,
        "command_raw": raw_cmd,
        "base": base,
        "length": len(cmd_stripped),
        "custom_name": _first(comp, ("CustomName",), (str,)) or "",
        "last_output": (_first(comp, ("LastOutput",), (str,)) or "")[:200],
        "powered": _flag(comp, ("powered",)),
        "success_count": _first(comp, ("successCount", "SuccessCount"), (int,)),
        "last_exec": _first(comp, ("LastExecution",), (int,)),
        "track_output": _flag(comp, ("TrackOutput",)),
        "source": source,
        "prio": prio,
        "fields": sorted(comp.keys()),
    }


def _value_compounds(value: bytes):
    """从一条记录的原始值里取出全部方块实体 NBT（必要时先解压）。"""
    comps = scan_compounds(value)
    if comps:
        return comps
    if value[:1] == bytes([TAG_COMPOUND]):
        return comps
    for fn in (snappy_uncompress, lambda b: zlib.decompress(b, -15), zlib.decompress):
        try:
            raw = fn(value)
        except Exception:
            continue
        if not raw or raw[:1] != bytes([TAG_COMPOUND]):
            continue
        comps = scan_compounds(raw)
        if comps:
            return comps
    return []


def extract_block_entities(records, want_entities=True, progress=None):
    """在合并后的记录里扫描方块实体，返回 (命令方块列表, 其它方块实体计数)"""
    p = progress or Progress()
    command_blocks = []
    template_blocks = []
    entity_counter = Counter()
    total = len(records) or 1
    step = max(1, total // 100)
    done = 0
    for key, (prio, value, source) in records.items():
        done += 1
        if done % step == 0 or done == total:
            p(60 + int(25 * done / total), "提取方块实体", "已扫描 %d/%d 条记录" % (done, total))
        if not value:
            continue
        if b"CommandBlock" not in value:
            if not want_entities or _ENTITY_PRE.search(value) is None:
                continue
        dim, cx, cz, _rtype = decode_chunk_key(key)
        chunk = (cx, cz)
        # structuretemplate_ 记录保存的是「结构蓝图」，其中的命令方块并未放置到世界，
        # 与已放置方块重复，因此单独归类、不计入总数。
        is_tpl = key[:18].lower().startswith(b"structuretemplate")
        for comp, _start, _end in _value_compounds(value):
            eid = comp.get("id")
            if not isinstance(eid, str):
                continue
            low = eid.lower()
            if "commandblock" in low:
                cb = make_command_block(comp, dim, chunk, source, prio)
                (template_blocks if is_tpl else command_blocks).append(cb)
            elif low in KNOWN_ENTITY_IDS and not is_tpl:
                entity_counter[eid] += 1
    return command_blocks, entity_counter, template_blocks


def dedupe_command_blocks(command_blocks):
    """同一坐标只保留最新写入的一条（同一方块的历史版本不重复计数）"""
    picked = OrderedDict()
    for cb in command_blocks:
        if cb["x"] is not None and cb["y"] is not None and cb["z"] is not None:
            key = (cb["dim"], cb["x"], cb["y"], cb["z"])
        else:
            key = ("raw", cb["command"], cb["chunk_x"], cb["chunk_z"], id(cb))
        old = picked.get(key)
        if old is None or cb["prio"] >= old["prio"]:
            picked[key] = cb
    return list(picked.values())


# ---------------------------------------------------------------------------
# 统计、风险提示与 CSV
# ---------------------------------------------------------------------------

DETAIL_COLUMNS = [
    "序号", "维度", "X", "Y", "Z", "区块X", "区块Z", "模式原始值", "模式",
    "有条件执行", "需要红石", "首次执行即运行", "延迟(刻)", "命令",
    "指令首词", "命令长度", "自定义名称", "空命令", "上次输出", "已激活",
    "成功次数", "上次执行刻", "数据来源",
]

SUMMARY_COLUMNS = ["项目", "数值"]
RANK_COLUMNS = ["类别", "名称", "数量", "占比"]
ENTITY_COLUMNS = ["方块实体类型", "数量", "占比"]

CSV_FILES = OrderedDict([
    ("detail", ("command_blocks_detail.csv", "命令方块明细", DETAIL_COLUMNS)),
    ("summary", ("command_blocks_summary.csv", "统计汇总", SUMMARY_COLUMNS)),
    ("rank", ("command_blocks_rank.csv", "指令/延迟排行", RANK_COLUMNS)),
    ("entities", ("block_entities_overview.csv", "其它方块实体概览", ENTITY_COLUMNS)),
])


def _yn(v):
    if v is None:
        return ""
    return "是" if int(v) != 0 else "否"


def _fmt_num(v):
    return "" if v is None else v


def detail_row(idx, cb):
    return [
        idx,
        DIM_NAMES.get(cb["dim"], "未知" if cb["dim"] is None else str(cb["dim"])),
        _fmt_num(cb["x"]), _fmt_num(cb["y"]), _fmt_num(cb["z"]),
        _fmt_num(cb["chunk_x"]), _fmt_num(cb["chunk_z"]),
        _fmt_num(cb["mode_raw"]), cb["mode"],
        _yn(cb["conditional"]), _yn(cb["redstone"]), _yn(cb["auto"]),
        _fmt_num(cb["tick_delay"]),
        cb["command"], cb["base"], cb["length"], cb["custom_name"],
        "是" if not cb["command"] else "否",
        cb["last_output"], _yn(cb["powered"]),
        _fmt_num(cb["success_count"]), _fmt_num(cb["last_exec"]), cb["source"],
    ]


def build_analysis(command_blocks, entity_counter, records_count, files_info,
                   world_info, warnings, elapsed, template_blocks=None):
    total = len(command_blocks)
    tpl_total = len(template_blocks or [])
    dim_counter = Counter()
    mode_counter = Counter()
    base_counter = Counter()
    cmd_counter = Counter()
    delay_counter = Counter()
    empty_cmd = slash_cmd = named = 0
    cond_n = red_n = auto_n = 0
    lengths = []
    bbox = {}
    unknown_base = []
    long_cmd = []
    for cb in command_blocks:
        dim_counter[DIM_NAMES.get(cb["dim"], "未知")] += 1
        mode_counter[cb["mode"] or "未记录"] += 1
        if cb["command"]:
            base_counter[cb["base"] or "(空)"] += 1
            cmd_counter[cb["command"]] += 1
            lengths.append(cb["length"])
            if cb["length"] > 256:
                long_cmd.append(cb)
            if cb["base"] and cb["base"] not in KNOWN_COMMANDS:
                unknown_base.append(cb)
        else:
            empty_cmd += 1
        if cb["command_raw"].startswith("/"):
            slash_cmd += 1
        if cb["custom_name"]:
            named += 1
        if cb["conditional"]:
            cond_n += 1
        if cb["redstone"]:
            red_n += 1
        if cb["auto"]:
            auto_n += 1
        if cb["tick_delay"] is not None:
            delay_counter[cb["tick_delay"]] += 1
        if cb["x"] is not None and cb["y"] is not None and cb["z"] is not None:
            d = DIM_NAMES.get(cb["dim"], "未知")
            b = bbox.setdefault(d, [cb["x"], cb["x"], cb["y"], cb["y"], cb["z"], cb["z"]])
            b[0] = min(b[0], cb["x"]); b[1] = max(b[1], cb["x"])
            b[2] = min(b[2], cb["y"]); b[3] = max(b[3], cb["y"])
            b[4] = min(b[4], cb["z"]); b[5] = max(b[5], cb["z"])

    duplicates = [(c, n) for c, n in cmd_counter.most_common() if n >= 2]
    avg_len = round(sum(lengths) / len(lengths), 1) if lengths else 0

    risks = []
    if empty_cmd:
        risks.append("有 %d 个命令方块尚未填写指令（空命令），建议确认是否为废弃残留。" % empty_cmd)
    if slash_cmd:
        risks.append("有 %d 条指令以“/”开头；基岩版命令方块内一般不写斜杠，可能不会生效。" % slash_cmd)
    if duplicates:
        risks.append("有 %d 条指令被重复使用（最高重复 %d 次），多为批量复制粘贴，注意后期维护成本。"
                     % (len(duplicates), duplicates[0][1]))
    if unknown_base:
        sample = "、".join(sorted({c["base"] for c in unknown_base})[:5])
        risks.append("有 %d 条指令的首词不在常见指令表中（如 %s），存在拼写错误或版本不兼容的可能。"
                     % (len(unknown_base), sample))
    if long_cmd:
        risks.append("有 %d 条指令长度超过 256 字符，个别输入框/版本可能被截断。" % len(long_cmd))
    fast_repeat = [cb for cb in command_blocks
                   if cb["mode_raw"] == 1 and (cb["tick_delay"] in (0, None))]
    if fast_repeat:
        risks.append("有 %d 个循环命令方块延迟为 0 刻（每刻执行），容易造成性能压力。" % len(fast_repeat))
    if tpl_total:
        risks.insert(0, "另有 %d 个命令方块保存在 structuretemplate_ 结构模板记录中"
                        "（属于蓝图内容、并非已放置方块），已单列且未计入总数。" % tpl_total)
    if total == 0:
        risks = ["本次没有解析到任何命令方块：请确认上传的是基岩版存档（.mcworld）"
                 "或 db 目录下的 .ldb / .log 文件。"
                 "Java 版存档使用 region(.mca) 格式，本工具不支持。"]
    elif not risks:
        risks.append("未发现明显的指令书写或配置风险。")

    summary_rows = [
        ["世界名称", world_info.get("LevelName") or "(未读取到)"],
        ["levelname.txt", files_info.get("levelname_txt") or ""],
        ["随机种子 RandomSeed", world_info.get("RandomSeed", "")],
        ["存储版本 StorageVersion", world_info.get("StorageVersion", "")],
        ["游戏模式 GameType", world_info.get("GameType", "")],
        ["统计的数据库文件数", files_info.get("db_file_count", 0)],
        ["解析到的 LevelDB 记录数", records_count],
        ["命令方块总数", total],
        ["结构模板内的命令方块（蓝图内容，未计入总数）", tpl_total],
        ["其它方块实体总数", sum(entity_counter.values())],
        ["其它方块实体种类数", len(entity_counter)],
    ]
    for name, cnt in dim_counter.most_common():
        summary_rows.append(["维度分布 - %s" % name, cnt])
    for name, cnt in mode_counter.most_common():
        summary_rows.append(["模式分布 - %s" % name, cnt])
    summary_rows += [
        ["有条件执行（LPCondionalMode）", cond_n],
        ["需要红石激活（LPRedstoneMode）", red_n],
        ["首次执行即运行（ExecuteOnFirstTick）", auto_n],
        ["空命令方块数", empty_cmd],
        ["带自定义名称的方块数", named],
        ["不带自定义名称的方块数", total - named],
        ["去重后的不同指令数", len(cmd_counter)],
        ["重复使用的指令条数", len(duplicates)],
        ["指令平均长度", avg_len],
        ["指令最长长度", max(lengths) if lengths else 0],
        ["指令总字符数", sum(lengths)],
        ["统计耗时(秒)", round(elapsed, 2)],
    ]
    for d, b in bbox.items():
        summary_rows.append(["坐标范围 - %s" % d,
                             "X %d~%d / Y %d~%d / Z %d~%d" % (b[0], b[1], b[2], b[3], b[4], b[5])])
    summary_rows += [
        ["统计口径-数据来源", "存档 LevelDB 方块实体（含 .ldb 表与 .log 日志，同编号以日志为准）"],
        ["统计口径-去重规则", "同一维度同一坐标只计一次，保留最新写入的版本"],
        ["统计口径-模式标签", "按 LPCommandMode 数值推断（0 脉冲 / 1 循环 / 2 连锁），请以原始值为准"],
    ]

    rank_rows = []
    for name, cnt in base_counter.most_common(30):
        rank_rows.append(["指令首词", name, cnt, round(cnt / max(1, len(lengths)) * 100, 1)])
    for cmd, cnt in duplicates[:20]:
        rank_rows.append(["重复指令", cmd[:120], cnt, round(cnt / max(1, total) * 100, 1)])
    for delay, cnt in delay_counter.most_common(15):
        rank_rows.append(["延迟(刻)", delay, cnt, round(cnt / max(1, total) * 100, 1)])

    entity_rows = []
    ent_total = sum(entity_counter.values())
    for name, cnt in entity_counter.most_common(30):
        entity_rows.append([name, cnt, round(cnt / max(1, ent_total) * 100, 1)])

    result = {
        "generated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        "elapsed": round(elapsed, 3),
        "world": world_info,
        "files": files_info.get("file_list", []),
        "records": records_count,
        "total": total,
        "kpi": {
            "total": total,
            "empty": empty_cmd,
            "conditional": cond_n,
            "redstone": red_n,
            "auto": auto_n,
            "named": named,
            "unique_commands": len(cmd_counter),
            "duplicates": len(duplicates),
            "avg_length": avg_len,
            "max_length": max(lengths) if lengths else 0,
            "other_entities": ent_total,
            "template_blocks": tpl_total,
        },
        "dimension": [{"name": k, "count": v} for k, v in dim_counter.most_common()],
        "modes": [{"name": k, "count": v} for k, v in mode_counter.most_common()],
        "top_commands": [{"name": k, "count": v} for k, v in base_counter.most_common(12)],
        "duplicates": [{"command": c, "count": n} for c, n in duplicates[:20]],
        "bbox": [{"dim": d, "range": b} for d, b in bbox.items()],
        "risks": risks,
        "warnings": warnings,
        "summary_rows": summary_rows,
        "rank_rows": rank_rows,
        "entity_rows": entity_rows,
        "details": [detail_row(i + 1, cb) for i, cb in enumerate(command_blocks)],
    }
    return result


def to_csv_bytes(header, rows) -> bytes:
    buf = io.StringIO()
    writer = csv.writer(buf, lineterminator="\r\n")
    writer.writerow(header)
    for row in rows:
        writer.writerow(row)
    return buf.getvalue().encode("utf-8-sig")


def build_csv_bundle(result):
    return {
        "detail": to_csv_bytes(DETAIL_COLUMNS, result["details"]),
        "summary": to_csv_bytes(SUMMARY_COLUMNS, result["summary_rows"]),
        "rank": to_csv_bytes(RANK_COLUMNS, result["rank_rows"]),
        "entities": to_csv_bytes(ENTITY_COLUMNS, result["entity_rows"]),
    }


def write_csv_bundle(bundle, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    paths = []
    for kind in CSV_FILES:
        fname = CSV_FILES[kind][0]
        path = os.path.join(out_dir, fname)
        with open(path, "wb") as fh:
            fh.write(bundle[kind])
        paths.append(path)
    return paths


def analyze(files, progress=None, want_entities=True):
    """完整分析流程：输入文件列表 -> 结果字典（含 CSV 字节）"""
    t0 = time.time()
    p = progress or Progress()
    warnings = []
    p(2, "准备", "正在整理输入文件…")
    inputs = load_world_inputs(files, p)
    warnings.extend(inputs["warnings"])
    db_files = inputs["db_files"]
    world_info = {}
    if inputs["level_dat"]:
        try:
            info, _root = parse_level_dat(inputs["level_dat"])
            world_info = {k: v for k, v in info.items()
                          if not isinstance(v, str) or len(str(v)) < 200}
            if inputs.get("levelname_txt") and "LevelName" not in world_info:
                world_info["LevelName"] = inputs["levelname_txt"]
        except Exception as exc:
            warnings.append("level.dat 解析失败：%s" % exc)
    p(22, "解析 LevelDB", "共 %d 个数据库文件" % len(db_files))
    records, _parsed = collect_records(db_files, warnings, p)
    p(60, "提取方块实体", "已合并 %d 条唯一记录" % len(records))
    cbs, ent_counter, tpl_cbs = extract_block_entities(records, want_entities=want_entities, progress=p)
    raw_count = len(cbs)
    cbs = dedupe_command_blocks(cbs)
    if raw_count != len(cbs):
        p(86, "去重", "原始命中 %d 条，按坐标去重后 %d 条" % (raw_count, len(cbs)))
    files_info = {
        "db_file_count": len(db_files),
        "levelname_txt": inputs["levelname_txt"],
        "file_list": [{"name": name, "size": len(data)} for name, data in db_files][:400],
    }
    p(92, "统计汇总", "正在生成统计与 CSV…")
    result = build_analysis(cbs, ent_counter, len(records), files_info,
                            world_info, warnings, time.time() - t0, tpl_cbs)
    bundle = build_csv_bundle(result)
    result["csv_sizes"] = {k: len(v) for k, v in bundle.items()}
    result["csv_names"] = {k: CSV_FILES[k][0] for k in CSV_FILES}
    result["csv_labels"] = {k: CSV_FILES[k][1] for k in CSV_FILES}
    result["raw_hits"] = raw_count
    result["_csv"] = bundle
    p(100, "完成", "共 %d 个命令方块" % result["total"])
    return result


# ---------------------------------------------------------------------------
# 浏览器界面（内置 http.server，移动端优先）
# ---------------------------------------------------------------------------

PAGE_HTML = r"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#101418">
<title>基岩版命令方块统计</title>
<style>
:root{--bg:#0f1418;--card:#172026;--line:#26323a;--fg:#e8eef2;--muted:#9fb0bb;--accent:#57c05a;--warn:#f0b232}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI","Noto Sans SC",sans-serif;padding:0 12px calc(28px + env(safe-area-inset-bottom))}
header{position:sticky;top:0;z-index:9;background:linear-gradient(180deg,var(--bg) 72%,rgba(15,20,24,.85));padding:14px 12px 8px;margin:0 -12px}
h1{font-size:18px;margin:0 0 2px}
.sub{color:var(--muted);font-size:12.5px}
.card{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:14px;margin:12px 0}
.card h2{font-size:15px;margin:0 0 10px;display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.card h2 span.tag{font-size:11px;color:var(--muted);font-weight:400}
.drop{border:1.5px dashed var(--line);border-radius:12px;padding:18px 12px;text-align:center;color:var(--muted);font-size:13.5px}
.drop.hot{border-color:var(--accent);color:var(--fg)}
.btn{display:inline-flex;align-items:center;justify-content:center;min-height:46px;padding:0 16px;border-radius:11px;border:1px solid var(--line);background:#1e2a31;color:var(--fg);font-size:15px;font-weight:600;cursor:pointer}
.btn.primary{background:var(--accent);border-color:var(--accent);color:#06210a}
.btn:disabled{opacity:.45}
.row{display:flex;flex-wrap:wrap;gap:10px;margin-top:12px}
.row .btn{flex:1 1 46%}
.list{list-style:none;padding:0;margin:10px 0 0;font-size:13px}
.list li{display:flex;justify-content:space-between;gap:10px;padding:6px 0;border-bottom:1px dashed var(--line);word-break:break-all}
.list li:last-child{border-bottom:0}
.bar{height:9px;background:#22303a;border-radius:6px;overflow:hidden;margin-top:10px}
.bar>i{display:block;height:100%;width:0;background:var(--accent);transition:width .25s}
.msg{color:var(--muted);font-size:13px;margin-top:8px;min-height:19px}
.kpis{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.kpi{background:#1c272e;border:1px solid var(--line);border-radius:12px;padding:10px 12px}
.kpi b{display:block;font-size:22px;line-height:1.25}
.kpi em{font-style:normal;color:var(--muted);font-size:12px}
.bars p{display:flex;justify-content:space-between;font-size:13px;margin:8px 0 4px;gap:8px}
.bars p span:first-child{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.track{background:#22303a;border-radius:6px;height:8px;overflow:hidden}
.track>i{display:block;height:100%;background:linear-gradient(90deg,#3f8f4a,#7ad07d)}
.tablewrap{overflow-x:auto;-webkit-overflow-scrolling:touch;border:1px solid var(--line);border-radius:10px}
table{border-collapse:collapse;font-size:12.5px;min-width:640px}
th,td{padding:7px 9px;border-bottom:1px solid var(--line);text-align:left;white-space:nowrap;max-width:260px;overflow:hidden;text-overflow:ellipsis}
th{background:#1e2a31;position:sticky;top:0;font-weight:600}
tr:last-child td{border-bottom:0}
.risk{font-size:13.5px;padding:9px 11px;border-radius:10px;background:#20282c;border-left:3px solid var(--warn);margin:8px 0}
.dl{display:grid;grid-template-columns:1fr;gap:10px}
.dl a{display:flex;justify-content:space-between;align-items:center;gap:8px;min-height:46px;padding:0 14px;border-radius:11px;background:#1e2a31;border:1px solid var(--line);color:var(--fg);text-decoration:none;font-size:14px}
.dl a em{font-style:normal;color:var(--muted);font-size:12px}
.warnbox{font-size:12.5px;color:var(--warn);margin-top:8px;white-space:pre-wrap;word-break:break-all}
footer{color:var(--muted);font-size:12px;text-align:center;margin-top:18px;line-height:1.7}
.hidden{display:none!important}
</style>
</head>
<body>
<header>
  <h1>基岩版命令方块统计</h1>
  <div class="sub">上传存档 → 解析 LevelDB → 导出 CSV · 全程本地运行</div>
</header>

<main>
  <section class="card">
    <h2>1. 选择存档文件 <span class="tag">.mcworld / .zip / .ldb / .log / level.dat</span></h2>
    <div class="drop" id="drop">
      点击下方按钮选择文件，或把文件拖到这里<br>
      手机端可多选：存档（.mcworld），或 db 目录下的全部 .ldb / .log
    </div>
    <input id="file" type="file" multiple accept=".mcworld,.zip,.ldb,.sst,.log,.dat,application/octet-stream" class="hidden">
    <div class="row">
      <button class="btn" id="pick">选择文件</button>
      <button class="btn primary" id="run" disabled>开始统计</button>
    </div>
    <ul class="list" id="fileList"></ul>
    <div class="msg" id="tip">尚未选择文件</div>
  </section>

  <section class="card hidden" id="progressCard">
    <h2>2. 解析进度 <span class="tag" id="stage">准备</span></h2>
    <div class="bar"><i id="bar"></i></div>
    <div class="msg" id="progressMsg">…</div>
  </section>

  <section class="card hidden" id="resultCard">
    <h2>3. 统计结果 <span class="tag" id="elapsed"></span></h2>
    <div class="kpis" id="kpis"></div>
    <div class="warnbox" id="warnbox"></div>
    <div class="msg" id="worldInfo"></div>
  </section>

  <section class="card hidden" id="distCard">
    <h2>分布情况</h2>
    <div class="bars" id="distBars"></div>
  </section>

  <section class="card hidden" id="riskCard">
    <h2>风险与提示</h2>
    <div id="riskList"></div>
  </section>

  <section class="card hidden" id="detailCard">
    <h2>明细预览 <span class="tag" id="detailTag"></span></h2>
    <div class="tablewrap"><table id="detailTable"></table></div>
  </section>

  <section class="card hidden" id="downloadCard">
    <h2>4. 导出 CSV</h2>
    <div class="dl" id="downloads"></div>
    <div class="msg">CSV 为 UTF-8(BOM) 编码，Excel / WPS / 手机表格应用可直接打开。</div>
  </section>
</main>

<footer>
  文件仅在你的本地网络内传输，不会上传互联网<br>
  基岩版命令方块保存在存档数据库的方块实体中，不同版本结构略有差异，结果以实际存档为准
</footer>

<script>
(function(){
  var state={task:null,files:[],result:null};
  var $=function(id){return document.getElementById(id);};

  function human(n){ if(n<1024) return n+' B'; if(n<1048576) return (n/1024).toFixed(1)+' KB'; return (n/1048576).toFixed(1)+' MB'; }
  function el(tag,cls,text){ var d=document.createElement(tag); if(cls)d.className=cls; if(text!==undefined)d.textContent=text; return d; }

  function renderFiles(){
    var ul=$('fileList'); ul.innerHTML='';
    state.files.forEach(function(f){
      var li=document.createElement('li');
      li.appendChild(el('span',null,f.name));
      li.appendChild(el('span',null,human(f.size)));
      ul.appendChild(li);
    });
    var total=state.files.reduce(function(s,f){return s+f.size;},0);
    $('tip').textContent=state.files.length? ('已选择 '+state.files.length+' 个文件，共 '+human(total)+'，可开始统计') : '尚未选择文件';
    $('run').disabled=!state.files.length;
  }

  function setFiles(list){
    state.files=Array.prototype.slice.call(list).map(function(f){return {file:f,name:f.name,size:f.size};});
    renderFiles();
  }

  $('pick').onclick=function(){ $('file').click(); };
  $('file').onchange=function(e){ setFiles(e.target.files); };

  var drop=$('drop');
  ['dragenter','dragover'].forEach(function(ev){ drop.addEventListener(ev,function(e){e.preventDefault();drop.classList.add('hot');}); });
  ['dragleave','drop'].forEach(function(ev){ drop.addEventListener(ev,function(e){e.preventDefault();drop.classList.remove('hot');}); });
  drop.addEventListener('drop',function(e){ if(e.dataTransfer&&e.dataTransfer.files&&e.dataTransfer.files.length) setFiles(e.dataTransfer.files); });

  function setBar(pct,stage,msg){
    $('progressCard').classList.remove('hidden');
    $('bar').style.width=Math.max(0,Math.min(100,pct))+'%';
    $('stage').textContent=stage||'';
    if(msg) $('progressMsg').textContent=msg;
  }

  function uploadSequential(task){
    return new Promise(function(resolve,reject){
      var i=0;
      function next(){
        if(i>=state.files.length){ resolve(); return; }
        var item=state.files[i];
        var xhr=new XMLHttpRequest();
        xhr.open('POST','/api/upload?task='+encodeURIComponent(task)+'&name='+encodeURIComponent(item.name));
        xhr.upload.onprogress=function(e){
          if(e.lengthComputable){
            var pct=Math.round((i+e.loaded/e.total)/state.files.length*100);
            setBar(pct,'上传文件','正在上传 '+item.name+'（'+pct+'%）');
          }
        };
        xhr.onload=function(){
          if(xhr.status===200){ i++; next(); } else { reject(new Error('上传失败：'+(xhr.responseText||xhr.status))); }
        };
        xhr.onerror=function(){ reject(new Error('网络错误，上传中断')); };
        xhr.send(item.file);
      }
      next();
    });
  }

  function poll(task){
    fetch('/api/status?id='+encodeURIComponent(task)).then(function(r){return r.json();}).then(function(s){
      setBar(s.percent||0,s.stage||'',s.message||'');
      if(s.state==='done'){ finish(task); return; }
      if(s.state==='error'){
        setBar(100,'失败',(s.error||'解析失败'));
        $('tip').textContent='解析失败：'+(s.error||'');
        $('run').disabled=false;
        return;
      }
      setTimeout(function(){poll(task);},450);
    }).catch(function(err){ setBar(100,'失败','与服务连接中断：'+err.message); });
  }

  function bars(container,items){
    container.innerHTML='';
    if(!items.length){ container.appendChild(el('div','msg','暂无数据')); return; }
    var max=items.reduce(function(m,x){return Math.max(m,x.count);},1);
    items.forEach(function(it){
      var p=document.createElement('p');
      p.appendChild(el('span',null,it.name));
      p.appendChild(el('span',null,String(it.count)));
      container.appendChild(p);
      var t=el('div','track'); var bar=el('i');
      bar.style.width=(it.count/max*100)+'%'; t.appendChild(bar); container.appendChild(t);
    });
  }

  function renderResult(r){
    var k=r.kpi, kb=$('kpis'); kb.innerHTML='';
    [['命令方块总数',k.total],['空命令',k.empty],['有条件执行',k.conditional],['需红石激活',k.redstone],
     ['不同指令数',k.unique_commands],['重复指令条数',k.duplicates],['平均指令长度',k.avg_length],
     ['其它方块实体',k.other_entities]].forEach(function(pair){
      var d=el('div','kpi');
      d.appendChild(el('em',null,pair[0]));
      d.appendChild(el('b',null,String(pair[1])));
      kb.appendChild(d);
    });
    $('elapsed').textContent='耗时 '+r.elapsed+' 秒 · '+r.generated_at;
    $('resultCard').classList.remove('hidden');

    var w=r.world||{}, wi=[];
    if(w.LevelName) wi.push('世界：'+w.LevelName);
    if(w.RandomSeed!==undefined&&w.RandomSeed!=='') wi.push('种子：'+w.RandomSeed);
    wi.push('解析记录：'+r.records+' 条');
    $('worldInfo').textContent=wi.join(' · ');
    var wb=$('warnbox');
    wb.textContent=(r.warnings&&r.warnings.length)? ('解析提示：'+r.warnings.join('；')):'';

    bars($('distBars'), (r.dimension||[]).concat(r.modes||[]).concat((r.top_commands||[]).map(function(x){return {name:'指令 '+x.name,count:x.count};})));
    $('distCard').classList.remove('hidden');

    var rl=$('riskList'); rl.innerHTML='';
    (r.risks||[]).forEach(function(t){ rl.appendChild(el('div','risk',t)); });
    $('riskCard').classList.remove('hidden');

    var cols=r.detail_columns||[];
    var tb=$('detailTable'); tb.innerHTML='';
    if(r.details&&r.details.length){
      var thead=document.createElement('thead'); var tr=document.createElement('tr');
      cols.forEach(function(c){ tr.appendChild(el('th',null,String(c))); });
      thead.appendChild(tr); tb.appendChild(thead);
      var tbody=document.createElement('tbody');
      r.details.forEach(function(row){
        var t=document.createElement('tr');
        row.forEach(function(cell){ t.appendChild(el('td',null,cell===null||cell===undefined?'':String(cell))); });
        tbody.appendChild(t);
      });
      tb.appendChild(tbody);
      $('detailTag').textContent='预览 '+r.details.length+' 行 / 共 '+r.total+' 行';
      $('detailCard').classList.remove('hidden');
    }

    var dl=$('downloads'); dl.innerHTML='';
    Object.keys(r.downloads).forEach(function(kind){
      var d=r.downloads[kind];
      var a=document.createElement('a');
      a.href='/api/download?id='+encodeURIComponent(state.task)+'&kind='+kind;
      a.appendChild(el('span',null,d.label+' · '+d.name));
      a.appendChild(el('em',null,human(d.size)));
      dl.appendChild(a);
    });
    $('downloadCard').classList.remove('hidden');
  }

  function finish(task){
    fetch('/api/result?id='+encodeURIComponent(task)).then(function(r){return r.json();}).then(function(r){
      if(r.error){ $('tip').textContent=r.error; return; }
      state.result=r; renderResult(r);
      $('tip').textContent='统计完成，可下载 CSV，或重新选择文件再次统计。';
      $('run').disabled=false;
    }).catch(function(err){ $('tip').textContent='结果读取失败：'+err.message; });
  }

  $('run').onclick=function(){
    if(!state.files.length) return;
    $('run').disabled=true;
    ['resultCard','distCard','riskCard','detailCard','downloadCard'].forEach(function(id){ $(id).classList.add('hidden'); });
    state.task='t'+Date.now().toString(36)+Math.random().toString(36).slice(2,7);
    setBar(0,'上传文件','准备上传…');
    uploadSequential(state.task).then(function(){
      return fetch('/api/run?task='+encodeURIComponent(state.task),{method:'POST'});
    }).then(function(){
      setBar(1,'解析中','服务端开始解析存档…');
      poll(state.task);
    }).catch(function(err){
      setBar(100,'失败',err.message);
      $('tip').textContent=err.message;
      $('run').disabled=false;
    });
  };
})();
</script>
</body>
</html>
"""


TASKS = {}
TASKS_LOCK = threading.Lock()


def _task_get(tid):
    with TASKS_LOCK:
        return TASKS.get(tid)


class StatsHandler(BaseHTTPRequestHandler):
    server_version = "MCCBStats/" + VERSION
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        if os.environ.get("MCCB_VERBOSE"):
            sys.stderr.write("[web] %s - %s\n" % (self.address_string(), fmt % args))

    # -- 响应工具 ---------------------------------------------------------
    def _send(self, code, body, ctype="text/plain; charset=utf-8", extra=None):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        if extra:
            for k, v in extra.items():
                self.send_header(k, v)
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _json(self, obj, code=200):
        self._send(code, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                   "application/json; charset=utf-8")

    def _query(self):
        return parse_qs(urlparse(self.path).query)

    # -- GET --------------------------------------------------------------
    def do_GET(self):
        path = urlparse(self.path).path
        q = self._query()
        if path in ("/", "/index.html"):
            self._send(200, PAGE_HTML.encode("utf-8"), "text/html; charset=utf-8")
            return
        if path == "/api/status":
            t = _task_get((q.get("id") or [""])[0])
            if not t:
                self._json({"state": "error", "error": "任务不存在或已过期"}, 404)
                return
            self._json({k: t.get(k) for k in ("state", "percent", "stage", "message", "error")})
            return
        if path == "/api/result":
            t = _task_get((q.get("id") or [""])[0])
            if not t or t.get("state") != "done":
                self._json({"error": "结果尚未就绪"}, 404)
                return
            r = t["result"]
            self._json({
                "generated_at": r["generated_at"], "elapsed": r["elapsed"],
                "world": r["world"], "records": r["records"], "total": r["total"],
                "kpi": r["kpi"], "dimension": r["dimension"], "modes": r["modes"],
                "top_commands": r["top_commands"], "duplicates": r["duplicates"],
                "bbox": r["bbox"], "risks": r["risks"], "warnings": r["warnings"][:20],
                "detail_columns": DETAIL_COLUMNS,
                "details": r["details"][:300],
                "downloads": {k: {"name": r["csv_names"][k], "label": r["csv_labels"][k],
                                  "size": r["csv_sizes"][k]} for k in CSV_FILES},
            })
            return
        if path == "/api/download":
            t = _task_get((q.get("id") or [""])[0])
            kind = (q.get("kind") or ["detail"])[0]
            if not t or t.get("state") != "done" or kind not in CSV_FILES:
                self._send(404, b"not found")
                return
            data = t["result"]["_csv"][kind]
            fname = CSV_FILES[kind][0]
            ascii_name = re.sub(r"[^A-Za-z0-9._-]", "_", fname)
            self._send(200, data, "text/csv; charset=utf-8", {
                "Content-Disposition":
                    'attachment; filename="%s"; filename*=UTF-8\'\'%s' % (ascii_name, fname),
            })
            return
        self._send(404, b"404")

    # -- POST -------------------------------------------------------------
    def do_POST(self):
        path = urlparse(self.path).path
        q = self._query()
        if path == "/api/run":
            tid = (q.get("task") or [""])[0]
            t = _task_get(tid)
            if not t:
                self._json({"error": "任务不存在"}, 404)
                return
            t["state"] = "running"
            threading.Thread(target=_run_task, args=(tid,), daemon=True).start()
            self._json({"ok": True})
            return
        if path == "/api/upload":
            tid = (q.get("task") or [""])[0]
            name = (q.get("name") or ["file"])[0]
            try:
                length = int(self.headers.get("Content-Length") or 0)
            except ValueError:
                length = 0
            max_bytes = self.server.max_upload_mb * 1024 * 1024
            if length > max_bytes:
                self._json({"error": "文件超过 %d MB 上限" % self.server.max_upload_mb}, 413)
                return
            data = self.rfile.read(length) if length else b""
            with TASKS_LOCK:
                t = TASKS.get(tid)
                if t is None:
                    t = TASKS[tid] = {
                        "state": "created", "percent": 0, "stage": "准备",
                        "message": "", "error": None, "files": [], "result": None,
                        "created": time.time(),
                    }
                t["files"].append((name, data))
            self._json({"ok": True, "received": len(data)})
            return
        self._send(404, b"404")


def _run_task(tid):
    t = _task_get(tid)
    if not t:
        return

    def cb(percent, stage, message):
        t["percent"] = percent
        t["stage"] = stage
        t["message"] = message

    try:
        result = analyze(list(t["files"]), progress=cb)
        t["result"] = result
        t["state"] = "done"
        t["files"] = []
    except Exception as exc:
        import traceback
        t["state"] = "error"
        t["error"] = "%s: %s" % (type(exc).__name__, exc)
        t["message"] = traceback.format_exc()[-500:]
    with TASKS_LOCK:
        now = time.time()
        for k in [k for k, v in TASKS.items() if now - v.get("created", now) > 6 * 3600]:
            TASKS.pop(k, None)


def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        s.close()


def serve(host="0.0.0.0", port=8765, max_mb=1024):
    httpd = ThreadingHTTPServer((host, port), StatsHandler)
    httpd.max_upload_mb = max_mb
    ip = lan_ip()
    print("=" * 64)
    print(" %s  v%s" % (APP_NAME, VERSION))
    print("=" * 64)
    print(" 电脑打开 : http://127.0.0.1:%d" % port)
    if host in ("0.0.0.0", "::"):
        print(" 手机打开 : http://%s:%d    （手机与电脑连同一 WiFi）" % (ip, port))
    print(" 上传上限 : %d MB；统计结果只保存在内存中，服务退出即清除" % max_mb)
    print(" 停止服务 : Ctrl + C")
    print("-" * 64)
    print(" 用法建议：手机端直接上传 .mcworld 存档（文件管理器里能直接找到）；")
    print("           若只有 db 目录，请把 0000xx.ldb 与 0000xx.log 一起多选上传。")
    print("-" * 64)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n已停止服务。")
    finally:
        httpd.server_close()


# ---------------------------------------------------------------------------
# 自检：构造合成存档，验证 snappy / LevelDB / NBT / 统计全链路
# ---------------------------------------------------------------------------

def _enc_payload(tag, val):
    if tag == TAG_STRING:
        b = val.encode("utf-8")
        return len(b).to_bytes(2, "little") + b
    if tag == TAG_BYTE:
        return bytes([val & 0xFF])
    if tag == TAG_SHORT:
        return struct.pack("<h", val)
    if tag == TAG_INT:
        return struct.pack("<i", val)
    if tag == TAG_LONG:
        return struct.pack("<q", val)
    raise ValueError("unsupported tag %r" % tag)


def _enc_compound(name, fields):
    """构造基岩版小端 NBT 的「带名字的 Compound」字节流"""
    nb = name.encode("utf-8")
    out = bytearray([TAG_COMPOUND]) + len(nb).to_bytes(2, "little") + nb
    for tag, fname, val in fields:
        fb = fname.encode("utf-8")
        out.append(tag)
        out += len(fb).to_bytes(2, "little") + fb
        out += _enc_payload(tag, val)
    out.append(TAG_END)
    return bytes(out)


def _build_sst(pairs, compress=False):
    """构造最小可用的 LevelDB SST 文件（自检用）"""
    buf = bytearray()
    index_entries = []
    for i in range(0, len(pairs), 4):
        chunk = pairs[i:i + 4]
        body = bytearray()
        last = b""
        for k, v in chunk:
            body += encode_uvarint(0) + encode_uvarint(len(k)) + encode_uvarint(len(v)) + k + v
            last = k
        body += struct.pack("<II", 0, 1)  # restart[0]=0，num_restarts=1（写在块末尾）
        stored = snappy_compress_literal(bytes(body)) if compress else bytes(body)
        ctype = BLOCK_SNAPPY if compress else BLOCK_NONE
        off = len(buf)
        buf += stored + bytes([ctype]) + struct.pack("<I", zlib.crc32(stored) & 0xFFFFFFFF)
        index_entries.append((last, encode_uvarint(off) + encode_uvarint(len(stored) + 5)))
    idx_body = bytearray()
    for k, v in index_entries:
        idx_body += encode_uvarint(0) + encode_uvarint(len(k)) + encode_uvarint(len(v)) + k + v
    idx_body += struct.pack("<II", 0, 1)
    idx_off = len(buf)
    idx_stored = bytes(idx_body)
    buf += idx_stored + bytes([BLOCK_NONE]) + struct.pack("<I", zlib.crc32(idx_stored) & 0xFFFFFFFF)
    footer = (encode_uvarint(0) + encode_uvarint(0) +
              encode_uvarint(idx_off) + encode_uvarint(len(idx_stored) + 5))
    footer += b"\x00" * (40 - len(footer)) + _SST_MAGIC
    buf += footer
    return bytes(buf)


def _build_log(pairs):
    """构造含一条 FULL 记录的 LevelDB WAL 文件（自检用）"""
    payload = bytearray()
    for k, v in pairs:
        payload += encode_uvarint(len(k)) + k + encode_uvarint(len(v)) + v
    payload = bytes(payload)
    header = struct.pack("<I", zlib.crc32(bytes([1]) + payload) & 0xFFFFFFFF) + \
        struct.pack("<H", len(payload)) + bytes([1])
    return header + payload


def _subchunk_value(nbt_blobs):
    """伪造子区块载荷：[版本][若干存储字节][内嵌方块实体 NBT]"""
    return b"\x08" + b"\x00" * 24 + b"".join(nbt_blobs) + b"\x00"


def _key(cx, cz, dim, y=0):
    # 真实基岩版区块键：[chunkX][chunkZ][dimension][类型字节][子区块序号]
    return struct.pack("<iii", cx, cz, dim) + bytes([0x2F, y & 0xFF])


def selftest():
    ok = True

    def check(label, cond, extra=""):
        nonlocal ok
        print(("  [OK]   " if cond else "  [FAIL] ") + label + ("  " + extra if extra else ""))
        if not cond:
            ok = False

    print("-- 1. snappy 解压（literal 与 copy 两条路径）")
    check("literal 往返", snappy_uncompress(snappy_compress_literal(b"hello mc")) == b"hello mc")
    crafted = b"\x0c" + b"\x0c" + b"abcd" + b"\x11" + b"\x04"
    check("copy 标签", snappy_uncompress(crafted) == b"abcdabcdabcd", repr(snappy_uncompress(crafted)))
    long_lit = bytes(range(256)) * 3
    check("长 literal", snappy_uncompress(snappy_compress_literal(long_lit)) == long_lit)

    print("-- 2. LevelDB 读写（SST + WAL）")
    cb1 = _enc_compound("", [
        (TAG_STRING, "id", "CommandBlock"), (TAG_INT, "x", 10), (TAG_INT, "y", 64),
        (TAG_INT, "z", 20), (TAG_STRING, "Command", "say hello"),
        (TAG_INT, "LPCommandMode", 0), (TAG_INT, "TickDelay", 0),
        (TAG_STRING, "CustomName", "欢迎"),
    ])
    chest = _enc_compound("", [
        (TAG_STRING, "id", "Chest"), (TAG_INT, "x", 1), (TAG_INT, "y", 63), (TAG_INT, "z", 1),
    ])
    cb2_old = _enc_compound("", [
        (TAG_STRING, "id", "CommandBlock"), (TAG_INT, "x", 11), (TAG_INT, "y", 64),
        (TAG_INT, "z", 20), (TAG_STRING, "Command", "say old version"),
        (TAG_INT, "LPCommandMode", 0), (TAG_INT, "TickDelay", 0),
    ])
    k1 = _key(0, 0, 0, 0)
    k2 = _key(0, 0, 0, 1)
    pairs = [(k1, _subchunk_value([cb1])), (k2, _subchunk_value([chest, cb2_old]))]
    sst = _build_sst(pairs, compress=True)
    got = dict(read_sst_entries(sst))
    check("SST(snappy) 读取", len(got) == 2, "entries=%d" % len(got))
    check("SST 数据命中 NBT", b"CommandBlock" in got.get(k1, b""))

    upd_cb = _enc_compound("", [
        (TAG_STRING, "id", "CommandBlock"), (TAG_INT, "x", 11), (TAG_INT, "y", 64),
        (TAG_INT, "z", 20), (TAG_STRING, "Command", "execute @a ~ ~ ~ tp @s ~ ~20 ~"),
        (TAG_INT, "LPCommandMode", 1), (TAG_INT, "LPRedstoneMode", 1),
        (TAG_INT, "TickDelay", 5),
    ])
    empty_cb = _enc_compound("", [
        (TAG_STRING, "id", "CommandBlock"), (TAG_INT, "x", 12), (TAG_INT, "y", 64),
        (TAG_INT, "z", 20), (TAG_STRING, "Command", ""), (TAG_INT, "LPCommandMode", 2),
    ])
    log_pairs = [(_key(0, 0, 0, 2), _subchunk_value([upd_cb, empty_cb]))]
    log = _build_log(log_pairs)
    log_entries = []
    for rec in iter_log_records(log):
        log_entries.extend(iter_write_batch(rec))
    check("WAL 记录读取", len(log_entries) == 1, "entries=%d" % len(log_entries))

    print("-- 3. .mcworld 全链路分析")
    level_dat = struct.pack("<ii", 10, 0) + _enc_compound("", [
        (TAG_STRING, "LevelName", "自检世界"), (TAG_LONG, "RandomSeed", 12345),
        (TAG_INT, "StorageVersion", 10),
    ])
    nether_cb = _enc_compound("", [
        (TAG_STRING, "id", "CommandBlock"), (TAG_INT, "x", 100), (TAG_INT, "y", 70),
        (TAG_INT, "z", -30), (TAG_STRING, "Command", "/give @a diamond 1"),
        (TAG_INT, "LPCommandMode", 0),
    ])
    here = os.path.dirname(os.path.abspath(__file__))
    zpath = os.path.join(here, "_selftest_world.mcworld")
    with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("db/CURRENT", "MANIFEST-000005\n")
        zf.writestr("db/000003.ldb", sst)
        zf.writestr("db/000004.ldb", _build_sst([(_key(1, 1, 1, 0), _subchunk_value([nether_cb]))]))
        zf.writestr("db/000004.log", log)
        zf.writestr("level.dat", level_dat)
        zf.writestr("levelname.txt", "自检世界")
    with open(zpath, "rb") as fh:
        data = fh.read()
    result = analyze([("_selftest_world.mcworld", data)])
    print("     命令方块 %d 个 / 其它方块实体 %d 个 / 合并记录 %d 条"
          % (result["total"], result["kpi"]["other_entities"], result["records"]))
    check("命令方块总数 = 4", result["total"] == 4, "实际 %d" % result["total"])
    check("坐标去重（原始命中 5 → 去重 4）", result["raw_hits"] == 5,
          "原始命中 %d" % result["raw_hits"])
    check("世界名解析", result["world"].get("LevelName") == "自检世界")
    check("记录数 >= 4", result["records"] >= 4, "实际 %d" % result["records"])
    by_pos = {(d[2], d[3], d[4]): d for d in result["details"]}
    cb2 = by_pos.get((11, 64, 20))
    check("WAL 覆盖旧版本", cb2 is not None and "~20" in cb2[13] and "old version" not in cb2[13],
          str(cb2[13]) if cb2 else "未找到更新后的方块")
    check("维度识别（下界）", any(d[1] == "下界" for d in result["details"]))
    check("自定义名称解析", any(d[16] == "欢迎" for d in result["details"]))
    check("空命令识别", result["kpi"]["empty"] >= 1, "empty=%d" % result["kpi"]["empty"])
    check("首斜杠指令提示", any("斜杠" in r for r in result["risks"]))
    check("CSV 明细行数 = 总数+1",
          len(result["_csv"]["detail"].decode("utf-8-sig").strip().splitlines()) == result["total"] + 1)
    check("CSV 含 UTF-8 BOM", result["_csv"]["summary"][:3] == b"\xef\xbb\xbf")
    outdir = os.path.join(here, "_selftest_out")
    paths = write_csv_bundle(result["_csv"], outdir)
    check("CSV 落盘", len(paths) == 4 and all(os.path.getsize(p) > 0 for p in paths))
    try:
        os.remove(zpath)
        for p in paths:
            os.remove(p)
        os.rmdir(outdir)
    except OSError:
        pass
    print("-- 自检结果：%s" % ("全部通过" if ok else "存在失败项"))
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# 命令行入口
# ---------------------------------------------------------------------------

def _print_result(result):
    print("世界名称      : %s" % (result["world"].get("LevelName") or "(未读取到)"))
    print("解析记录数    : %d" % result["records"])
    print("命令方块总数  : %d" % result["total"])
    for row in result["summary_rows"]:
        if str(row[0]).startswith(("维度分布", "模式分布", "空命令", "重复使用", "指令平均长度")):
            print("%-14s: %s" % (row[0], row[1]))
    print("风险与提示    :")
    for r in result["risks"]:
        print("  - %s" % r)
    if result["warnings"]:
        print("解析提示      :")
        for w in result["warnings"][:10]:
            print("  - %s" % w)


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Minecraft 基岩版地图命令方块统计工具（单文件 / 纯标准库）")
    ap.add_argument("-f", "--file", action="append", default=[],
                    help="要分析的存档或 LevelDB 文件（可重复，支持通配符）")
    ap.add_argument("-o", "--out", default="mc_cb_csv_out",
                    help="CSV 输出目录（默认 mc_cb_csv_out）")
    ap.add_argument("--json", default="", help="额外导出 JSON 统计结果到指定文件")
    ap.add_argument("--host", default="0.0.0.0", help="网页服务监听地址（默认 0.0.0.0）")
    ap.add_argument("--port", type=int, default=8765, help="网页服务端口（默认 8765）")
    ap.add_argument("--max-mb", type=int, default=1024, help="单文件上传上限 MB（默认 1024）")
    ap.add_argument("--no-entities", action="store_true", help="跳过其它方块实体统计（更快）")
    ap.add_argument("--selftest", action="store_true", help="运行内置自检后退出")
    args = ap.parse_args(argv)

    if args.selftest:
        return selftest()

    if args.file:
        import glob
        files = []
        for pattern in args.file:
            for path in (glob.glob(pattern) or [pattern]):
                try:
                    with open(path, "rb") as fh:
                        files.append((os.path.basename(path), fh.read()))
                    print("已载入 %s" % path)
                except OSError as exc:
                    print("无法读取 %s：%s" % (path, exc))
        if not files:
            print("没有可读取的文件。")
            return 2

        def progress(percent, stage, message):
            sys.stdout.write("\r[%3d%%] %-12s %s" % (percent, stage, message[:56]))
            sys.stdout.flush()

        result = analyze(files, progress=progress, want_entities=not args.no_entities)
        print()
        _print_result(result)
        paths = write_csv_bundle(result["_csv"], args.out)
        print("CSV 已导出    :")
        for p in paths:
            print("  - %s" % p)
        if args.json:
            with open(args.json, "w", encoding="utf-8") as fh:
                json.dump({k: v for k, v in result.items() if not k.startswith("_")},
                          fh, ensure_ascii=False, indent=2)
            print("JSON 已导出   : %s" % args.json)
        return 0

    serve(args.host, args.port, args.max_mb)
    return 0


if __name__ == "__main__":
    sys.exit(main())
