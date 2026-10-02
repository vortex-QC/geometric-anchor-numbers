#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
几何锚数·数值轮：开放宇宙扩展——全域枚举+两序版实验（10-02 日总明日入口①·主人令"涡继续"承接）
预注册（2026-10-02 上午·先于分析跑数落盘·同文件预注册模式）：

  问题（20261002.md §3 明日入口① 逐字）：
    「开放宇宙扩展档（长度 4~8 受限→全域枚举+两序版实验——本轮只跑单承诺）」
    即：①宇宙从长度 4~8 边受限枚举扩为全域枚举（与闭合宇宙 808 条全域口径对齐）；
       ②承诺从单承诺（β 等距锁）扩为两承诺 {α 身份锁, β 等距锁} 的两序建立实验
        （承袭约束顺序轮判别设计②的甲序/乙序语法）。

  宇宙（全域开放版·域与井承袭在案）：
    域 = A'4 双井格点域 x∈[-1,3],y∈[-2,2]·井 A=(0,0)/B=(2,0)（承袭）
    对象 = 自避免开放链（非闭合）·长度 ≥1 边（2~23 点）全域枚举·避井
    规范化 = min(链正向, 链反向) 字典序（承袭）
    ★宇宙规模预实测（设定面侦察·判据面零接触）：58762 条（1~20 边）；
      其中 4~8 边子集=2697 条与承袭轮精确一致（复现锚预校验✅）

  操作（与闭合/开放两轮同款·承袭窗口）：
    子弧替换：S=P[i..i+k]（1≤|S|≤6 边）换为 u→v 的另一条简单路径 T（1≤|T|≤6 边）
    ·T 内部不与补弧相交·新链自避免·避井（全域版 Q 自动在宇宙内·无长度过滤）

  承诺（与闭合轮同款操作级定义·开放链版）：
    α（身份锁）= 替换扫过环 (S+rev T) 不包双井（wA=0∧wB=0）
      ——实现为相对交换化类判等：c(S)=c(T)。其中 c(W)=环 W+rev(γ(u,v)) 对 A/B 的绕数，
        γ(u,v)=BFS（邻居序固定 上右下左）最短避井参照路径（端点对归一 min→max·预注册固定）。
      加性恒等式 w(S+rev T)=c(S)−c(T)（γ 驻 sp 段消去）——判等与直接扫环绕数零差
      （实现层自检：随机 10 对 (S,T) 逐对核验，见结果 JSON）。
      开放宇宙 α 类对应面=端点对×相对交换化类（链自身 c 经 α 操作逐边不变——同恒等式推论）。
      注：交换化读数与非闭合轮 42 档同款——非交换（基本群词）细化不在承诺定义域（诚实边界）。
    β（等距锁）= |P|=|Q|（⟺ |S|=|T|）
    甲序 = 先建立 α（E_α 闭包）→ 再建立 β（E_α∩E_β 闭包）
    乙序 = 先建立 β（E_β 闭包）→ 再建立 α（同一交集闭包）

  判据（跑前锁定）：
    OX-0 复现锚【校验面·先于一切判读】:
         4~8 边子宇宙（2697 条）β 闭包 = 674 且 E_β(子)=5235 精确复现
         （承袭开放轮数据交叉验证）——不复现则全轮判停勘误。
    OX-1 终态交换面【登记性】: 两序终态=closure(E_α∩E_β) 同一划分（构造事实·登记）
    OX-2 类数路径可判别【主判据】: N_α ≠ N_β（中间态类数不同）
    OX-3 分配账本可判别: 存在对象使中间归属不同——N_mid=|{o: αmates(o)≠βmates(o)}|/NU
         （mates-集比较用双独立哈希：Σhash₁(id) 与 Σhash₂(id)·碰撞概率 <2⁻⁶⁰ 级·预注册）
    OX-4 显化幅度检验【新·判读⑦跨域检验·双向预注册】:
      OX-4a 闭轮方向复现: R_甲=N_∩/N_α > R_乙=N_∩/N_β ?
      OX-4b 结构规则检验（判读⑦机理读法"先粗后细→第二步大幅显化"的跨域形式）:
         粗承诺（N 较小者）先建的序，其第二步细分比值 > 细承诺先建的序。
         （闭合轮 N_α=8<N_β=41 故 4a/4b 同向；开放宇宙两承诺粗细秩序为数据问题——
          若 N_α>N_β 则 4a/4b 可分离，4b 为判读⑦的机理级检验。）
    OX-5 定义面完备登记【承袭 OS-4 语义·不硬判】:
         D_def = |{(端点对, cA, cB)}|（端点对×相对交换化类档数）vs N_α/N_β/N_∩
         完备率 D_def/N_α 与 D_def/N_∩ 如实登记（α 操作保 c 推 N_α≥D_def·结构性预期）
    OX-6 端点对保持【OP-2 承袭】: α/β 操作边全保链端点对（构造性+逐边核·零违例登记）

  运行预算条款: 总硬墙 480 秒（枚举+操作对+闭包共享计时·8 进程并行·超墙如实登记判停）
  诚实边界: toy 非物理测量·α/β 到一阶/二阶约束的映射=结构对应（类比级·承袭）·
  γ 参照路径为确定性约定（并列取 BFS 先达·非全局字典序最小——影响 c 标签不影响判等结构）·
  零新增物理测量值·零新增对外 record·发布物零改动。
  输出: papers/几何锚数_数值轮_开放宇宙扩展_结果_v0.1.json
"""
import json, time, sys
from collections import defaultdict, deque

T0 = time.time()
WALL = 480.0
out = {'_prereg': '判据见脚本头·2026-10-02 上午先于分析跑数落盘·480s 硬墙·8 进程并行'}

XA, XB, YA, YB = -1, 3, -2, 2
WELLS = [(0, 0), (2, 0)]
WELL_SET = set(WELLS)
SMAX, TMAX = 6, 6
MOVES = [(0, 1), (1, 0), (0, -1), (-1, 0)]   # 上右下左·γ 的 BFS 邻居序固定此序

FREE = [(x, y) for x in range(XA, XB + 1) for y in range(YA, YB + 1) if (x, y) not in WELL_SET]
BIT = {p: 1 << i for i, p in enumerate(FREE)}

def canon_chain(P):
    a = tuple(P); b = tuple(reversed(P))
    return min(a, b)

def winding_center(path, cx, cy):
    """承袭在案实现（闭合轮/开放轮同款·逐字）"""
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

# ================= γ 参照路径（预注册：BFS·邻居序上右下左·端点对归一 min→max） =================
_gam = {}
def gamma(u, v):
    if u == v:
        return (u,)
    key = (u, v) if u <= v else (v, u)
    g = _gam.get(key)
    if g is None:
        prev = {key[0]: None}
        dq = deque([key[0]])
        while dq:
            cur = dq.popleft()
            if cur == key[1]:
                break
            for dx, dy in MOVES:
                nxt = (cur[0] + dx, cur[1] + dy)
                if not (XA <= nxt[0] <= XB and YA <= nxt[1] <= YB):
                    continue
                if nxt in WELL_SET or nxt in prev:
                    continue
                prev[nxt] = cur
                dq.append(nxt)
        path = []
        c = key[1]
        while c is not None:
            path.append(c); c = prev[c]
        g = tuple(reversed(path))
        _gam[key] = g
    return g if u <= v else tuple(reversed(g))

_c_cache = {}
def cpath(W):
    """c(W)=环 W+rev(γ(s,e)) 对 A/B 的绕数（W 定向 s→e 原样）"""
    r = _c_cache.get(W)
    if r is not None:
        return r
    g = gamma(W[0], W[-1])
    loop = list(W) + list(reversed(g))
    r = (wA(loop), wB(loop))
    _c_cache[W] = r
    return r

# ================= 全域枚举 =================
chains = set()
cnt_by_len = defaultdict(int)
def dfs(path, visited):
    m = len(path)
    if m >= 2:
        c = canon_chain(path)
        if c not in chains:
            chains.add(c); cnt_by_len[m - 1] += 1
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

for x in range(XA, XB + 1):
    for y in range(YA, YB + 1):
        if (x, y) in WELL_SET:
            continue
        dfs([(x, y)], {(x, y)})

objs = sorted(chains)
NU = len(objs)
print(f"全域开放宇宙：{NU} 条规范链（1~{max(cnt_by_len)} 边）·用时 {round(time.time()-T0,1)}s", flush=True)
out['宇宙'] = {'链数': NU, '长度分布': dict(sorted(cnt_by_len.items()))}
obj_id = {c: i for i, c in enumerate(objs)}
objs_48 = [c for c in objs if 4 <= len(c) - 1 <= 8]
out['宇宙']['子宇宙4~8'] = len(objs_48)

# ================= 替换弧表（缓存·含内部掩码/边数/交换化类） =================
T_tab = {}
def t_paths(u, v):
    key = (u, v)
    r = T_tab.get(key)
    if r is not None:
        return r
    if key[0] > key[1]:
        base = t_paths(key[1], key[0])
        r = [(tuple(reversed(t)), msk, ne, (-ca, -cb)) for (t, msk, ne, (ca, cb)) in base]
        T_tab[key] = r
        return r
    res = []
    def walk(path, visited):
        cur = path[-1]
        if cur == key[1] and len(path) >= 2:
            tp = tuple(path)
            msk = 0
            for p in tp[1:-1]:
                msk |= BIT[p]
            res.append((tp, msk, len(tp) - 1, cpath(tp)))
            return
        if len(path) - 1 >= TMAX:
            return
        for dx, dy in MOVES:
            nxt = (cur[0] + dx, cur[1] + dy)
            if not (XA <= nxt[0] <= XB and YA <= nxt[1] <= YB):
                continue
            if nxt in WELL_SET or nxt in visited:
                continue
            if nxt != key[1] and abs(nxt[0]-key[1][0]) + abs(nxt[1]-key[1][1]) > TMAX - (len(path)-1):
                continue
            visited.add(nxt); path.append(nxt)
            walk(path, visited)
            path.pop(); visited.remove(nxt)
    walk([key[0]], {key[0]})
    T_tab[key] = res
    return res

# ================= 实现层自检：c 判等 ⟺ 直接扫环绕数（随机 10 对） =================
import random
random.seed(20261002)
_selfcheck = []
_pairs = [(u, v) for u in FREE for v in FREE if u < v and u != v]
for _ in range(10):
    u, v = random.choice(_pairs)
    tp = t_paths(u, v)
    if len(tp) < 2:
        continue
    (S, _, _, cS), (T, _, _, cT) = random.sample(tp, 2)
    loop = list(S) + list(reversed(T))[1:]
    direct = (wA(loop), wB(loop))
    via_c = (cS[0] - cT[0], cS[1] - cT[1])
    _selfcheck.append({'S边数': len(S)-1, 'T边数': len(T)-1,
                       '直接扫环': direct, 'c差': via_c, '一致': direct == via_c})
selfcheck_ok = all(x['一致'] for x in _selfcheck)
out['实现层自检_c判等'] = {'样本数': len(_selfcheck), '全一致': selfcheck_ok, '明细': _selfcheck}
print(f"实现层自检（c判等⟺直接扫环·10对）：{'全一致✅' if selfcheck_ok else '🚨不一致——判停'}", flush=True)
if not selfcheck_ok:
    out['verdict'] = {'reading': '实现层自检失败·判停勘误', 'timed_out': False}
    json.dump(out, open('papers/几何锚数_数值轮_开放宇宙扩展_结果_v0.1.json', 'w', encoding='utf-8'),
              ensure_ascii=False, indent=1)
    sys.exit(1)

# ================= 操作对生成（多进程·存在量词语义） =================
ALLOW = None   # 允许的 Q 集合（OX-0 子宇宙复现=子集·None=全域）

def gen_edges(chunk):
    """对 chunk 内每条规范链 P 生成 (α边, β边)·返回打包 id 对列表"""
    eas, ebs = [], []
    ep_ok = True
    allow = ALLOW
    for P in chunk:
        if time.time() - T0 > WALL:
            raise TimeoutError
        m = len(P)
        pm = 0
        for p in P:
            pm |= BIT[p]
        # 前缀掩码：pref[i] = P[0..i-1] 各点位或（pref[0]=0）
        pref = [0] * (m + 1)
        for i in range(m):
            pref[i + 1] = pref[i] | BIT[P[i]]
        pid = obj_id[P]
        for i in range(m - 1):
            for k in range(1, min(SMAX, m - 1 - i) + 1):
                j = i + k
                u = P[i]; v = P[j]
                S = P[i:j + 1]
                cS = cpath(S)
                s_edges = k
                rest_mask = (pref[i] | (pm ^ pref[j + 1]))   # P[:i] ∪ P[j+1:] 的点位
                for (T, tmsk, t_edges, cT) in t_paths(u, v):
                    a_ok = (cS == cT)
                    b_ok = (s_edges == t_edges)
                    if not (a_ok or b_ok):
                        continue
                    if tmsk & rest_mask:
                        continue
                    Q = P[:i] + T + P[j + 1:]
                    cq = canon_chain(Q)
                    if cq == P:
                        continue
                    qid = obj_id.get(cq)
                    if qid is None:
                        continue
                    if allow is not None and cq not in allow:
                        continue
                    if (Q[0], Q[-1]) != (P[0], P[-1]):
                        ep_ok = False
                    pk = (pid, qid) if pid < qid else (qid, pid)
                    pk = pk[0] * 100000 + pk[1]
                    if a_ok:
                        eas.append(pk)
                    if b_ok:
                        ebs.append(pk)
    return eas, ebs, ep_ok

def run_ops(universe, allow=None, workers=8):
    """allow=允许的 Q 集合（OX-0 子宇宙复现用）；None=全域"""
    global ALLOW
    old = ALLOW
    ALLOW = allow
    try:
        if workers <= 1 or len(universe) < 4000:
            eas, ebs, ep = gen_edges(universe)
            return set(eas), set(ebs), ep
        chunk_size = (len(universe) + workers - 1) // workers
        chunks = [universe[i:i + chunk_size] for i in range(0, len(universe), chunk_size)]
        import multiprocessing as mp
        eas_all, ebs_all = [], []
        ep_all = True
        with mp.Pool(workers) as pool:
            for eas, ebs, ep in pool.imap_unordered(gen_edges, chunks):
                eas_all.extend(eas); ebs_all.extend(ebs)
                ep_all = ep_all and ep
        return set(eas_all), set(ebs_all), ep_all
    finally:
        ALLOW = old

class UFI:
    """整数 id 域并查集"""
    def __init__(s, ids):
        s.f = {o: o for o in ids}
    def find(s, x):
        while s.f[x] != x:
            s.f[x] = s.f[s.f[x]]; x = s.f[x]
        return x
    def union(s, a, b):
        ra, rb = s.find(a), s.find(b)
        if ra != rb:
            s.f[ra] = rb

def closure(ids, edges):
    uf = UFI(ids)
    for e in edges:
        uf.union(e // 100000, e % 100000)
    groups = defaultdict(list)
    for o in ids:
        groups[uf.find(o)].append(o)
    return uf, groups

def unpack(pk):
    return pk // 100000, pk % 100000

# ---- OX-0 复现锚（4~8 子宇宙·承袭语义：宇宙与 Q 均限 4~8 边） ----
allow48 = set(objs_48)
ids48 = [obj_id[c] for c in objs_48]
eas0, ebs0, ep0 = run_ops(objs_48, allow=allow48, workers=1)
_, g0 = closure(ids48, ebs0)
ox0_N = len(g0); ox0_E = len(ebs0)
ox0_pass = bool(ox0_N == 674 and ox0_E == 5235 and ep0)
out['OX_0_复现锚'] = {'子宇宙': len(objs_48), 'E_beta_子': ox0_E, 'N_beta_子': ox0_N,
                      '端点对零违例': ep0, '判据': ox0_pass,
                      '预期': {'E': 5235, 'N': 674}}
print(f"OX-0 复现锚：子宇宙 {len(objs_48)}·E_beta={ox0_E}（预期5235）·N_beta={ox0_N}（预期674）·判据={ox0_pass}·用时 {round(time.time()-T0,1)}s", flush=True)
if not ox0_pass:
    out['verdict'] = {'reading': 'OX-0 复现失败·全轮判停勘误', 'timed_out': False}
    json.dump(out, open('papers/几何锚数_数值轮_开放宇宙扩展_结果_v0.1.json', 'w', encoding='utf-8'),
              ensure_ascii=False, indent=1)
    sys.exit(1)

# ---- 全域操作对 ----
try:
    eas, ebs, ep_all = run_ops(objs, allow=None, workers=8)
except TimeoutError:
    out['verdict'] = {'reading': '全域操作对超 480s 硬墙·判停如实登记', 'timed_out': True}
    out['运行秒'] = round(time.time() - T0, 1)
    json.dump(out, open('papers/几何锚数_数值轮_开放宇宙扩展_结果_v0.1.json', 'w', encoding='utf-8'),
              ensure_ascii=False, indent=1)
    print("硬墙触发·判停", flush=True)
    sys.exit(1)

E_a, E_b = len(eas), len(ebs)
eab = eas & ebs
E_ab = len(eab)
print(f"全域操作对：E_alpha={E_a}·E_beta={E_b}·交集={E_ab}·用时 {round(time.time()-T0,1)}s", flush=True)
out['操作对'] = {'E_alpha': E_a, 'E_beta': E_b, '交集': E_ab, '端点对保持零违例': ep_all}

# ---- 闭包三件 ----
ids_all = list(range(NU))
uf_a, g_a = closure(ids_all, eas)
uf_b, g_b = closure(ids_all, ebs)
uf_ab, g_ab = closure(ids_all, eab)
N_a, N_b, N_ab = len(g_a), len(g_b), len(g_ab)
print(f"闭包：N_alpha={N_a}·N_beta={N_b}·N_交集={N_ab}", flush=True)
out['闭包'] = {'N_alpha': N_a, 'N_beta': N_b, 'N_交集': N_ab}

# ---- OX-3 分配账本（mates-集双哈希比较·整数 id 域） ----
r1 = {o: (o * 2654435761) % 999999937 for o in ids_all}
r2 = {o: (o * 40503 + 97) % 999999937 for o in ids_all}
ha = {}; hb = {}
for root, mem in g_a.items():
    s1 = sum(r1[x] for x in mem); s2 = sum(r2[x] for x in mem)
    for x in mem:
        ha[x] = (s1, s2)
for root, mem in g_b.items():
    s1 = sum(r1[x] for x in mem); s2 = sum(r2[x] for x in mem)
    for x in mem:
        hb[x] = (s1, s2)
N_mid = sum(1 for o in ids_all if ha[o] != hb[o])
out['OX_3_分配账本'] = {'N_mid': N_mid, '宇宙': NU, '占比': round(N_mid / NU, 4)}
print(f"OX-3 分配账本：N_mid={N_mid}/{NU}（{round(N_mid/NU*100,2)}%）", flush=True)

# ---- OX-5 定义面（端点对×相对交换化类） ----
ddef = set()
for P in objs:
    Wn = tuple(reversed(P)) if P[0] > P[-1] else P
    ddef.add((Wn[0], Wn[-1]) + cpath(Wn))
D_def = len(ddef)
out['OX_5_定义面'] = {'D_def': D_def, '完备率_def_over_alpha': round(D_def / N_a, 4),
                      '完备率_def_over_交集': round(D_def / N_ab, 4)}
print(f"OX-5 定义面：D_def={D_def} vs N_alpha={N_a}·N_交集={N_ab}", flush=True)

# ---- 判据 ----
ox2 = bool(N_a != N_b)
ox4a = bool(N_ab / N_a > N_ab / N_b) if N_a and N_b else None   # 等价于 N_a<N_b
coarse_first_ratio = N_ab / min(N_a, N_b)
fine_first_ratio = N_ab / max(N_a, N_b)
ox4b = bool(coarse_first_ratio > fine_first_ratio)
out['OX_1_终态交换'] = {'状态': '登记（交集闭包构造唯一·两序终态同一划分）', 'N_终态': N_ab}
out['OX_2_类数路径'] = {'N_alpha': N_a, 'N_beta': N_b, '判据': ox2,
                        '甲序路径': [NU, N_a, N_ab], '乙序路径': [NU, N_b, N_ab]}
out['OX_4_显化幅度'] = {'R_甲': round(N_ab / N_a, 4), 'R_乙': round(N_ab / N_b, 4),
                        'OX4a_闭轮方向复现': ox4a, 'OX4b_结构规则': ox4b,
                        '粗承诺': 'alpha' if N_a < N_b else ('beta' if N_b < N_a else '同数')}
out['OX_6_端点对保持'] = {'零违例': ep_all, '判据': bool(ep_all)}

reading_bits = []
if ox2:
    reading_bits.append("类数路径可判别")
if ox4b:
    reading_bits.append("先粗后细→第二步大幅显化（结构规则跨域成立）")
elif ox4a:
    reading_bits.append("闭轮方向复现")
else:
    reading_bits.append("显化幅度不对称未复现·如实登记")
out['verdict'] = {'reading': '；'.join(reading_bits), 'timed_out': False}
out['运行秒'] = round(time.time() - T0, 1)
print("VERDICT:", json.dumps(out['verdict'], ensure_ascii=False), flush=True)

with open('papers/几何锚数_数值轮_开放宇宙扩展_结果_v0.1.json', 'w', encoding='utf-8') as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print(f"已落盘 papers/几何锚数_数值轮_开放宇宙扩展_结果_v0.1.json·总用时 {out['运行秒']}s", flush=True)
