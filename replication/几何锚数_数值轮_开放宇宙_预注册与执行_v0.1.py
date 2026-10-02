#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
几何锚数·数值轮：开放路径宇宙——去闭合前提的机制运转检验（第四轮档判别设计①）+欧拉相容轻件（判别④）
预注册（2026-10-01 深夜·先于跑数落盘·同文件预注册模式）：

  问题（二阶约束显化机制档 §五/§六 逐字）：
    闭合问答案=「闭合性是一阶承诺的面级强化（独立维度），不是多面体身份的必要条件」
    判别①=开放路径宇宙顺序轮：去掉闭合前提重跑承诺建立实验——机制（碎裂+分配）
    不依赖闭合的 toy 验证。
    判别④=欧拉相容轻件：闭合宇宙 76 碎片内 (wA,wB) 坐标唯一（两承诺合取共存）。

  宇宙（开放版·域与井承袭在案件）：
    域 = A'4 双井格点域 x∈[-1,3],y∈[-2,2]·井 A=(0,0)/B=(2,0)（承袭）
    对象 = 自避免开放链（非闭合）·长度（边数）4~8·全起全枚举·避井
    规范化 = min(链正向, 链反向) 字典序（开放链无旋转对称·反转对称）
    拓扑身份 = 端点对（开放链无绕数不变量——绕数需闭合环）

  操作（与闭合版同款·开放链版）：
    子弧替换：S=P[i..i+k]（1≤k≤6）换为 u=p_i→v=p_{i+k} 的另一条简单路径 T
    （|T|≤6·T 内部不与补弧相交·新链自避免·避井·len(Q)∈[4,8]）
    E_iso（等距锁）= |P|=|Q|；开放宇宙无"双井锁"对应（无绕数可护——一阶承诺平凡的构造面）

  运行预算条款：60 秒硬墙（DFS+操作生成共享计时）——超墙如实登记已完成部分域

  判据（跑前锁定）：
    OP-1（机制运转·主判据）: 开放宇宙等距锁闭包类数 N_iso_open 满足 1 < N_iso_open < 宇宙数
         ——碎裂照样发生且非全孤立（承诺建立=可达空间碎裂的机制在开放宇宙运转）
    OP-2（一阶平凡性·对照面）: 全部操作边保端点对（构造性保证·零违例登记）
         ——对照：闭合宇宙一阶身份=绕数 7 档（非平凡）；开放宇宙一阶身份=端点对
         （自动保持·平凡）——**闭合承诺使一阶拓扑身份非平凡化**【本轮新判读·闭合问数值半边】
    OP-3（碎裂对照·登记性）: N_iso_open vs 闭合宇宙等距锁闭包 N_iso=41——如实登记不做硬判
    OP-4（欧拉相容轻件·闭合宇宙）: 76 碎片每片内 (wA,wB) 唯一
         ——两承诺合取共存的结构验证（判读③「显化在一阶骨架内进行」的格点版）

  判读：OP-1 ∧ OP-2 成立 → 机制不依赖闭合（碎裂+分配在开放宇宙照样运转）+
        闭合承诺的角色定位（价值在一阶身份非平凡化·不在二阶身份存在）——
        四问判读④「闭合不必须」获得数值面。
        OP-4 成立 → 判读③欧拉相容恒等式获格点验证。

  诚实边界：toy 非物理测量·端点对=开放链拓扑身份的格点对应（类比级）·
  零新增物理测量值·零新增对外 record·发布物零改动。
  输出：papers/几何锚数_数值轮_开放宇宙_结果_v0.1.json
"""
import json, time
from collections import defaultdict

T0 = time.time()
WALL = 60.0
out = {'_prereg': '判据见脚本头·2026-10-01 深夜先于跑数落盘·60s 硬墙条款'}

XA, XB, YA, YB = -1, 3, -2, 2
WELLS = [(0, 0), (2, 0)]
WELL_SET = set(WELLS)
SMAX, TMAX = 6, 6
LMIN, LMAX = 4, 8          # 开放链长度（边数）
MOVES = [(0, 1), (1, 0), (0, -1), (-1, 0)]

def winding_center(path, cx, cy):
    w = 0
    pts = list(path) + [path[0]]
    for (a, b), (c, d) in zip(pts, pts[1:]):
        ay, by = b - cy, d - cy
        ax, bx = a - cx, c - cx
        if ay <= 0 < by and ax * by - ay * bx > 0:
            w += 1
        elif ay > 0 >= by and ax * by - ay * bx < 0:
            w -= 1
    return w

wA = lambda p: winding_center(p, 0, 0)
wB = lambda p: winding_center(p, 2, 0)

def canon_chain(P):
    a = tuple(P); b = tuple(reversed(P))
    return min(a, b)

# ================= 开放自避免链枚举（长度 4~8·60s 硬墙） =================
chains_raw = set()
def dfs(path, visited):
    if time.time() - T0 > WALL:
        raise TimeoutError
    m = len(path)
    if m - 1 >= LMIN:
        chains_raw.add(canon_chain(path))
    if m - 1 >= LMAX:
        return
    cur = path[-1]
    for dx, dy in MOVES:
        nx, ny = cur[0] + dx, cur[1] + dy
        if not (XA <= nx <= XB and YA <= ny <= YB):
            continue
        nxt = (nx, ny)
        if nxt in WELL_SET or nxt in visited:
            continue
        visited.add(nxt); path.append(nxt)
        dfs(path, visited)
        path.pop(); visited.remove(nxt)

timed_out = False
try:
    for x in range(XA, XB + 1):
        for y in range(YA, YB + 1):
            if (x, y) in WELL_SET:
                continue
            if time.time() - T0 > WALL:
                raise TimeoutError
            dfs([(x, y)], {(x, y)})
except TimeoutError:
    timed_out = True

objs = sorted(chains_raw)
NU = len(objs)
print(f"开放宇宙：{NU} 条规范自避免链（长 {LMIN}~{LMAX} 边）·硬墙触发={timed_out}·用时 {round(time.time()-T0,1)}s")
out['宇宙'] = {'链数': NU, '长度档': [LMIN, LMAX], '硬墙触发': timed_out}

# ================= 替换弧表（承袭在案·缓存复用） =================
T_tab = {}
def t_paths(u, v):
    key = (u, v)
    if key in T_tab:
        return T_tab[key]
    if key[0] > key[1]:
        T_tab[key] = [tuple(reversed(t)) for t in t_paths(v, u)]
        return T_tab[key]
    res = []
    def walk(path, visited):
        cur = path[-1]
        if cur == v and len(path) >= 2:
            res.append(tuple(path)); return
        if len(path) - 1 >= TMAX:
            return
        for dx, dy in MOVES:
            nxt = (cur[0] + dx, cur[1] + dy)
            if not (XA <= nxt[0] <= XB and YA <= nxt[1] <= YB):
                continue
            if nxt in WELL_SET or nxt in visited:
                continue
            if nxt != v and abs(nxt[0]-v[0]) + abs(nxt[1]-v[1]) > TMAX - (len(path)-1):
                continue
            visited.add(nxt); path.append(nxt)
            walk(path, visited)
            path.pop(); visited.remove(nxt)
    walk([u], {u})
    T_tab[key] = res
    return res

# ================= 操作对生成（开放链·存在量词语义） =================
objset = set(objs)
impl_iso = {}   # (P,Q) -> beta_any（开放宇宙唯一承诺=等距锁）
ep_keep = True  # OP-2 端点对保持（构造性·登记）
for P in objs:
    if time.time() - T0 > WALL:
        raise TimeoutError
    m = len(P)
    for i in range(m):
        for k in range(1, min(SMAX, m - 1 - i) + 1):
            u = P[i]; v = P[i + k]  # 开放链无取模·k 界保证 i+k≤m-1
            S_ends = (u, v)
            j = i + k
            # 补弧 = 链去掉子弧 S 的两段：P[:i] + P[j+1:]
            rest_set = set(P[:i]) | set(P[j+1:])
            for T in t_paths(u, v):
                Ti = T[1:-1]
                if Ti and rest_set.intersection(Ti):
                    continue
                Q = tuple(P[:i]) + tuple(T) + tuple(P[j+1:])
                if len(Q) - 1 < LMIN or len(Q) - 1 > LMAX:
                    continue
                if len(set(Q)) != len(Q):
                    continue
                cq = canon_chain(Q)
                if cq == P or cq not in objset:
                    continue
                # OP-2：链端点对保持（构造性断言·逐边核）
                #【勘误留痕 2026-10-01 首跑】检验对象写错：首版比对 (Q[0],Q[-1])≠(P[i],P[i+k])
                #  （被替换弧端点）——中间弧时必假；正确对象=链端点对 (P[0],P[-1])：
                #  T 以 u 起点以 v 终点·Q=P[:i]+T+P[j+1:]·链端构造性保持（含链端替换：
                #  i=0 时 Q[0]=T[0]=u=P[0]）
                if (Q[0], Q[-1]) != (P[0], P[-1]):
                    ep_keep = False
                pk = (P, cq) if P <= cq else (cq, P)
                if len(P) == len(cq):
                    impl_iso[pk] = True

edges_iso = sorted(impl_iso.keys())
print(f"操作对（等距锁·开放宇宙）：{len(edges_iso)} · 用时 {round(time.time()-T0,1)}s")
out['操作对'] = {'E_iso_open': len(edges_iso), '端点对保持零违例': ep_keep}

# ================= 并查集闭包 =================
class UF:
    def __init__(s):
        s.f = {o: o for o in objs}
    def find(s, x):
        while s.f[x] != x:
            s.f[x] = s.f[s.f[x]]; x = s.f[x]
        return x
    def union(s, a, b):
        ra, rb = s.find(a), s.find(b)
        if ra != rb:
            s.f[ra] = rb

def closure(edges):
    uf = UF()
    for a, b in edges:
        uf.union(a, b)
    groups = defaultdict(int)
    for o in objs:
        groups[uf.find(o)] += 1
    return len(groups)

if not timed_out:
    N_iso_open = closure(edges_iso)
    print(f"等距锁闭包类数（开放宇宙）：N_iso_open={N_iso_open}")
    out['闭包'] = {'N_iso_open': N_iso_open}
else:
    N_iso_open = None
    out['闭包'] = {'N_iso_open': '未完成·硬墙截断'}

# ================= OP-4 欧拉相容轻件（闭合宇宙·复用约束顺序轮数据） =================
# 重算闭合宇宙交集闭包 76 类，检验每类 (wA,wB) 唯一
import itertools
cycles_raw = set()
def dfs_c(path, visited):
    start = path[0]; cur = path[-1]
    for dx, dy in MOVES:
        nx, ny = cur[0] + dx, cur[1] + dy
        if not (XA <= nx <= XB and YA <= ny <= YB):
            continue
        nxt = (nx, ny)
        if nxt in WELL_SET:
            continue
        if nxt == start and len(path) >= 4:
            cycles_raw.add(tuple(path)); continue
        if nxt in visited:
            continue
        visited.add(nxt); path.append(nxt)
        dfs_c(path, visited)
        path.pop(); visited.remove(nxt)

def canon_cyc(cyc):
    m = len(cyc)
    return min(cyc[i:] + cyc[:i] for i in range(m))

for x in range(XA, XB + 1):
    for y in range(YA, YB + 1):
        if (x, y) in WELL_SET:
            continue
        dfs_c([(x, y)], {(x, y)})
cobjs = sorted({canon_cyc(c) for c in cycles_raw})

T_tab2 = {}
def t_paths2(u, v):
    key = (u, v)
    if key in T_tab2:
        return T_tab2[key]
    if key[0] > key[1]:
        T_tab2[key] = [tuple(reversed(t)) for t in t_paths2(v, u)]
        return T_tab2[key]
    res = []
    def walk(path, visited):
        cur = path[-1]
        if cur == v and len(path) >= 2:
            res.append(tuple(path)); return
        if len(path) - 1 >= TMAX:
            return
        for dx, dy in MOVES:
            nxt = (cur[0] + dx, cur[1] + dy)
            if not (XA <= nxt[0] <= XB and YA <= nxt[1] <= YB):
                continue
            if nxt in WELL_SET or nxt in visited:
                continue
            if nxt != v and abs(nxt[0]-v[0]) + abs(nxt[1]-v[1]) > TMAX - (len(path)-1):
                continue
            visited.add(nxt); path.append(nxt)
            walk(path, visited)
            path.pop(); visited.remove(nxt)
    walk([u], {u})
    T_tab2[key] = res
    return res

impl_both = {}
cinv = {c: (wA(c), wB(c)) for c in cobjs}
for P in cobjs:
    m = len(P)
    for i in range(m):
        for k in range(1, min(SMAX, m - 1) + 1):
            u = P[i]; v = P[(i + k) % m]
            S = P[i:i+k] if i + k <= m else P[i:] + P[:i+k]
            j = (i + k) % m
            arc2 = [P[(j + t) % m] for t in range(m - k + 1)]
            arc2_set = set(arc2)
            for T in t_paths2(u, v):
                Ti = T[1:-1]
                if Ti and arc2_set.intersection(Ti):
                    continue
                Q = (tuple(T) + tuple(arc2[1:]))[:-1]
                if len(Q) < 4 or len(set(Q)) != len(Q):
                    continue
                cq = canon_cyc(Q)
                if cq == P or cq not in cinv:
                    continue
                pk = (P, cq) if P <= cq else (cq, P)
                rec = impl_both.get(pk)
                if rec is None:
                    rec = [False, False]
                    impl_both[pk] = rec
                loop = list(S) + list(reversed(T))[1:]
                if wA(loop) == 0 and wB(loop) == 0:
                    rec[0] = True
                if len(P) == len(cq):
                    rec[1] = True

edges_both = [pk for pk, (a, b) in impl_both.items() if a and b]
uf = UF.__new__(UF); uf.f = {o: o for o in cobjs}
def find(x):
    while uf.f[x] != x:
        uf.f[x] = uf.f[uf.f[x]]; x = uf.f[x]
    return x
for a, b in edges_both:
    ra, rb = find(a), find(b)
    if ra != rb:
        uf.f[ra] = rb
frag = defaultdict(set)
for o in cobjs:
    frag[find(o)].add(cinv[o])
mixed = [r for r, s in frag.items() if len(s) > 1]
op4 = bool(len(frag) == 76 and not mixed)
out['OP_4_欧拉相容'] = {'碎片数': len(frag), '绕数混片数': len(mixed), '判据': op4}
print(f"OP-4 欧拉相容（闭合宇宙）：碎片数={len(frag)}（预期76）·绕数混片={len(mixed)}·判据={op4}")

# ================= 判据 =================
if not timed_out:
    op1 = bool(1 < N_iso_open < NU)
    out['OP_1_机制运转'] = {'N_iso_open': N_iso_open, '宇宙': NU, '判据': op1}
    print(f"OP-1 机制运转：1 < {N_iso_open} < {NU}  判据={op1}")
    op2 = bool(ep_keep)
    out['OP_2_一阶平凡性'] = {'端点对保持零违例': ep_keep, '判据': op2}
    print(f"OP-2 一阶平凡性（端点对自动保持·对照闭合绕数7档非平凡）：判据={op2}")
    op3 = '登记' if N_iso_open is not None else '未完成'
    out['OP_3_碎裂对照'] = {'N_iso_open': N_iso_open, '闭合宇宙N_iso': 41, '状态': op3}
    print(f"OP-3 碎裂对照：开放 {N_iso_open} vs 闭合 41（登记性）")
else:
    out['OP_1_机制运转'] = {'状态': '硬墙截断·如实登记'}
    out['OP_2_一阶平凡性'] = {'状态': '硬墙截断·如实登记'}
    out['OP_3_碎裂对照'] = {'状态': '硬墙截断·如实登记'}

reading = ("机制不依赖闭合+闭合承诺使一阶身份非平凡化——闭合问「不必须」获数值面"
           if not timed_out and out.get('OP_1_机制运转', {}).get('判据') and op2 and op4
           else ("部分完成·欧拉相容面已验·开放宇宙面硬墙截断" if timed_out
                 else "判负/部分未过·如实登记"))
out['verdict'] = dict(reading=reading, timed_out=timed_out)
out['运行秒'] = round(time.time() - T0, 1)
print("VERDICT:", json.dumps(out['verdict'], ensure_ascii=False))

with open('papers/几何锚数_数值轮_开放宇宙_结果_v0.1.json', 'w', encoding='utf-8') as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print("已落盘 papers/几何锚数_数值轮_开放宇宙_结果_v0.1.json")
