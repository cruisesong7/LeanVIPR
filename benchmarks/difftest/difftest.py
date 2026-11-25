#!/usr/bin/env python3
"""Differential testing of VIPR checkers.

Mutates known-valid VIPR certificates and compares the verdicts of several checkers
(LeanVIPR, upstream viprchk, viprchk_parallel, ...). Mutations are either
meaning-preserving (number respelling, term order, comments, labels), where every
checker must keep the seed's verdict, or invalidating edits (multipliers, senses,
indices, integrality, claims), where disagreements are triaged. For small problems an
exact ground-truth solver decides whether the mutated claim is actually true, so an
acceptance of a false claim is reported as a soundness failure.

Usage:
  difftest.py --checker NAME=CMD ... --seeds FILES... --cases N --out DIR
where CMD contains `{}` for the certificate path. Exit codes are mapped to verdicts by
`classify` (LeanVIPR: 0 pass, 1 parse error, 2 reject; viprchk: 0 pass, else reject).
"""

import argparse
import itertools
import json
import os
import random
import re
import shlex
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction as Q

# ----------------------------------------------------------------------------------
# Numbers

def parse_num(s):
    """Exact value of a VIPR number token, or None. Accepts decimals and p/q with signs."""
    m = re.fullmatch(r'([+-]?)(\d*)(?:\.(\d*))?', s)
    if m and (m.group(2) or m.group(3)):
        v = Q(int(m.group(2) or '0')) + (Q(int(m.group(3)), 10 ** len(m.group(3))) if m.group(3) else 0)
        return -v if m.group(1) == '-' else v
    m = re.fullmatch(r'([+-]?\d+)/([+-]?\d+)', s)
    if m and int(m.group(2)) != 0:
        return Q(int(m.group(1)), int(m.group(2)))
    return None


def canon(q):
    q = Q(q)
    return str(q.numerator) if q.denominator == 1 else f'{q.numerator}/{q.denominator}'


def respell(q, rng, kinds=None):
    """An equivalent but differently written spelling of q, with its kind."""
    q = Q(q)
    p, d = q.numerator, q.denominator
    opts = [('scaled', f'{p * 2}/{d * 2}'), ('scaled', f'{p * 3}/{d * 3}')]
    if p != 0: opts.append(('negden', f'{-p}/{-d}'))
    if p >= 0:
        opts.append(('plus', f'+{canon(q)}'))
        opts.append(('zeros', '0' + canon(q) if d == 1 else f'0{p}/{d}'))
    # finite decimal if the denominator is 2^a 5^b
    dd = d
    while dd % 2 == 0: dd //= 2
    while dd % 5 == 0: dd //= 5
    if dd == 1:
        k = 0
        while (10 ** k) % d: k += 1
        num = p * (10 ** k // d)
        sign = '-' if num < 0 else ''
        digits = str(abs(num)).rjust(k + 1, '0')
        dec = digits[:-k] + '.' + digits[-k:] if k else digits + '.0'
        opts.append(('decimal', sign + dec))
    kind, text = rng.choice(opts)
    if kinds is not None: kinds.add(kind)
    return text

# ----------------------------------------------------------------------------------
# Certificate model: tokens with roles, so mutations can target fields precisely.

def tokenize(text):
    out = []
    for line in text.split('\n'):
        for tok in line.split():
            if tok.startswith('%'):
                break
            out.append(tok)
    return out


class Cert:
    """A parsed certificate. Numbers keep their original spelling."""

    def __init__(self, text):
        t = tokenize(text)
        self.pos = 0
        self.t = t
        nxt = self.next
        assert nxt() == 'VER'; self.ver = nxt()
        assert nxt() == 'VAR'; n = int(nxt()); self.vars = [nxt() for _ in range(n)]
        assert nxt() == 'INT'; k = int(nxt()); self.ints = [nxt() for _ in range(k)]
        assert nxt() == 'OBJ'; self.objsense = nxt(); self.obj = self.pairs(int(nxt()))
        assert nxt() == 'CON'; m = int(nxt()); self.nbound = nxt()
        self.cons = [self.row() for _ in range(m)]
        assert nxt() == 'RTP'; kind = nxt()
        self.rtp = ['infeas'] if kind == 'infeas' else ['range', nxt(), nxt()]
        assert nxt() == 'SOL'; s = int(nxt())
        self.sols = [[nxt(), self.pairs(int(nxt()))] for _ in range(s)]
        assert nxt() == 'DER'; d = int(nxt())
        self.ders = []
        for _ in range(d):
            r = self.row()
            r['reason'] = self.reason()
            r['idx'] = nxt()
            if self.pos < len(t) and t[self.pos] in ('global', 'local'):
                r['scope'] = nxt()
            self.ders.append(r)

    def next(self):
        tok = self.t[self.pos]; self.pos += 1; return tok

    def pairs(self, k):
        return [[self.next(), self.next()] for _ in range(k)]

    def row(self):
        name, sense, rhs = self.next(), self.next(), self.next()
        body = self.next()
        body = 'OBJ' if body == 'OBJ' else self.pairs(int(body))
        return {'name': name, 'sense': sense, 'rhs': rhs, 'body': body}

    def reason(self):
        assert self.next() == '{'
        kw = self.next()
        if kw in ('asm', 'sol'):
            assert self.next() == '}'; return [kw]
        if kw == 'uns':
            r = ['uns'] + [self.next() for _ in range(4)]
            assert self.next() == '}'; return r
        if kw in ('lin', 'rnd'):
            nx = self.next()
            if nx == 'weak':
                assert self.next() == '{'
                nb = int(self.next())
                bounds = [[self.next() for _ in range(4)] for _ in range(nb)]
                assert self.next() == '}'
                comb = self.pairs(int(self.next()))
                assert self.next() == '}'; return ['linweak', bounds, comb]
            comb = self.pairs(int(nx))
            assert self.next() == '}'; return [kw, comb]
        raise ValueError('unknown reason ' + kw)

    # -- printing
    def render(self, comments=False, rng=None):
        L = []
        if comments and rng:
            L.append('% generated by difftest')
        def emit(s, row=False):
            L.append(s + (f'   % c{len(L)}' if row and comments and rng and rng.random() < 0.3 else ''))
        def body(b):
            return 'OBJ' if b == 'OBJ' else ' '.join([str(len(b))] + [f'{i} {c}' for i, c in b])
        def reason(r):
            if r[0] in ('asm', 'sol'): return '{ ' + r[0] + ' }'
            if r[0] == 'uns': return '{ uns ' + ' '.join(r[1:]) + ' }'
            if r[0] in ('lin', 'rnd'):
                return '{ ' + r[0] + ' ' + str(len(r[1])) + ''.join(f' {i} {c}' for i, c in r[1]) + ' }'
            if r[0] == 'linweak':
                b = ' '.join(' '.join(x) for x in r[1])
                return ('{ lin weak { ' + str(len(r[1])) + (' ' + b if b else '') + ' } '
                        + str(len(r[2])) + ''.join(f' {i} {c}' for i, c in r[2]) + ' }')
            raise ValueError(r)
        emit(f'VER {self.ver}')
        emit(f'VAR {len(self.vars)}'); emit(' '.join(self.vars))
        emit(f'INT {len(self.ints)}'); emit(' '.join(self.ints))
        emit(f'OBJ {self.objsense}'); emit(body(self.obj))
        emit(f'CON {len(self.cons)} {self.nbound}')
        for c in self.cons:
            emit(f"{c['name']} {c['sense']} {c['rhs']} {body(c['body'])}", row=True)
        emit('RTP ' + ' '.join(self.rtp))
        emit(f'SOL {len(self.sols)}')
        for name, vals in self.sols:
            emit(f'{name} {len(vals)}' + ''.join(f' {i} {v}' for i, v in vals))
        emit(f'DER {len(self.ders)}')
        for d in self.ders:
            emit(f"{d['name']} {d['sense']} {d['rhs']} {body(d['body'])} {reason(d['reason'])} {d['idx']}"
                 + (' ' + d['scope'] if 'scope' in d else ''), row=True)
        return '\n'.join(L) + '\n'

# ----------------------------------------------------------------------------------
# Exact ground truth for small problems (bounded integers, Fourier-Motzkin for the rest)

def rows_le(cert):
    """Problem rows as (coeff dict, rhs) meaning sum <= rhs."""
    obj = {int(i): parse_num(c) for i, c in cert.obj}
    out = []
    for c in cert.cons:
        coef = obj if c['body'] == 'OBJ' else {}
        if c['body'] != 'OBJ':
            for i, a in c['body']:
                coef[int(i)] = coef.get(int(i), 0) + parse_num(a)
        rhs = parse_num(c['rhs'])
        if c['sense'] in ('L', 'E'): out.append((dict(coef), rhs))
        if c['sense'] in ('G', 'E'): out.append(({k: -v for k, v in coef.items()}, -rhs))
    return out


def fm_feasible(rows, elim):
    """Fourier-Motzkin: are the <= rows feasible over the variables `elim` (others fixed out)?"""
    rows = [(dict(c), r) for c, r in rows]
    for x in elim:
        pos = [(c, r) for c, r in rows if c.get(x, 0) > 0]
        neg = [(c, r) for c, r in rows if c.get(x, 0) < 0]
        rest = [(c, r) for c, r in rows if c.get(x, 0) == 0]
        new = []
        for (cp, rp) in pos:
            for (cn, rn) in neg:
                a, b = cp[x], -cn[x]
                c = {}
                for k in set(cp) | set(cn):
                    if k == x: continue
                    v = b * cp.get(k, 0) + a * cn.get(k, 0)
                    if v: c[k] = v
                new.append((c, b * rp + a * rn))
        rows = rest + new
        if len(rows) > 4000:
            return None
    return all(r >= 0 for c, r in rows)


def ground_truth(cert, box=6, limit=20000):
    """Exact truth of the claim for small problems, or None when not decidable here.

    Returns (feasible, optimum) where optimum is a Fraction, '-inf'/'inf' (unbounded), or
    None when infeasible."""
    try:
        n = len(cert.vars)
        ints = sorted({int(i) for i in cert.ints if 0 <= int(i) < n})
        if any(int(i) < 0 or int(i) >= n for i in cert.ints):
            return None
        rows = rows_le(cert)
        if any(k >= n or k < 0 for c, r in rows for k in c):
            return None
        # integer boxes from one-variable rows
        lo = {j: None for j in ints}; hi = {j: None for j in ints}
        for c, r in rows:
            if len(c) == 1:
                (k, a), = c.items()
                if k in lo:
                    b = r / a
                    if a > 0: hi[k] = b if hi[k] is None else min(hi[k], b)
                    else: lo[k] = b if lo[k] is None else max(lo[k], b)
        doms = []
        for j in ints:
            if lo[j] is None or hi[j] is None: return None
            import math
            a, b = math.ceil(lo[j]), math.floor(hi[j])
            if b - a > box: return None
            doms.append(range(a, b + 1) if a <= b else range(0))
        cont = [j for j in range(n) if j not in ints]
        obj = {int(i): parse_num(c) for i, c in cert.obj}
        best = None; feasible = False; count = 0
        for vals in itertools.product(*doms):
            count += 1
            if count > limit: return None
            fix = dict(zip(ints, vals))
            sub = []
            for c, r in rows:
                cc = {k: v for k, v in c.items() if k not in fix}
                rr = r - sum(v * fix[k] for k, v in c.items() if k in fix)
                sub.append((cc, rr))
            f = fm_feasible(sub, cont)
            if f is None: return None
            if not f: continue
            feasible = True
            # LP optimum of the objective over the continuous variables: project onto t
            T = -1
            o_fix = sum(obj.get(k, 0) * v for k, v in fix.items())
            oc = {k: v for k, v in obj.items() if k not in fix and v}
            # t = o_fix + oc.x  as two rows
            t_rows = sub + [({**oc, T: Q(-1)}, -o_fix), ({**{k: -v for k, v in oc.items()}, T: Q(1)}, o_fix)]
            lo_t, hi_t = project_bounds(t_rows, cont, T)
            if lo_t == 'err': return None
            val = lo_t if cert.objsense == 'min' else hi_t
            if cert.objsense == 'min':
                best = val if best is None else (val if val == '-inf' or (best != '-inf' and val < best) else best)
            else:
                best = val if best is None else (val if val == 'inf' or (best != 'inf' and val > best) else best)
        return (feasible, best)
    except Exception:
        return None


def project_bounds(rows, elim, t):
    rows = [(dict(c), r) for c, r in rows]
    for x in elim:
        pos = [(c, r) for c, r in rows if c.get(x, 0) > 0]
        neg = [(c, r) for c, r in rows if c.get(x, 0) < 0]
        rest = [(c, r) for c, r in rows if c.get(x, 0) == 0]
        new = []
        for (cp, rp) in pos:
            for (cn, rn) in neg:
                a, b = cp[x], -cn[x]
                c = {}
                for k in set(cp) | set(cn):
                    if k == x: continue
                    v = b * cp.get(k, 0) + a * cn.get(k, 0)
                    if v: c[k] = v
                new.append((c, b * rp + a * rn))
        rows = rest + new
        if len(rows) > 4000: return ('err', 'err')
    lo, hi = '-inf', 'inf'
    for c, r in rows:
        a = c.get(t, 0)
        if a > 0: hi = r / a if hi == 'inf' else min(hi, r / a)
        elif a < 0: lo = r / a if lo == '-inf' else max(lo, r / a)
    return lo, hi


def claim_true(cert, truth):
    """Is the certificate's claim true, given ground truth? None if unknown."""
    if truth is None: return None
    feasible, opt = truth
    if cert.rtp[0] == 'infeas':
        return not feasible
    lb = None if cert.rtp[1] == '-inf' else parse_num(cert.rtp[1])
    ub = None if cert.rtp[2] == 'inf' else parse_num(cert.rtp[2])
    if not feasible:
        return True  # no optimum: every bound holds vacuously (solutions are checked separately)
    if cert.objsense == 'min':
        ok_lb = lb is None or (opt != '-inf' and lb <= opt)
        ok_ub = ub is None or (opt != '-inf' and opt <= ub) or opt == '-inf'
        return ok_lb and ok_ub
    if cert.objsense == 'max':
        ok_ub = ub is None or (opt != 'inf' and opt <= ub)
        ok_lb = lb is None or (opt != 'inf' and lb <= opt) or opt == 'inf'
        return ok_lb and ok_ub
    return None

# ----------------------------------------------------------------------------------
# Mutations. Each returns a label; `preserving` mutations keep the meaning.

def num_fields(c):
    """References to every numeric field, as (container, key) pairs."""
    f = []
    for p in c.obj: f.append((p, 1))
    for r in c.cons + c.ders:
        f.append((r, 'rhs'))
        if r['body'] != 'OBJ':
            for p in r['body']: f.append((p, 1))
    for s in c.sols:
        for p in s[1]: f.append((p, 1))
    for d in c.ders:
        if d['reason'][0] in ('lin', 'rnd'):
            for p in d['reason'][1]: f.append((p, 1))
        if d['reason'][0] == 'linweak':
            for p in d['reason'][2]: f.append((p, 1))
    if c.rtp[0] == 'range':
        for k in (1, 2):
            if c.rtp[k] not in ('inf', '-inf'): f.append((c.rtp, k))
    return f


def m_respell(c, rng):
    f = num_fields(c)
    if not f: return None
    kinds = set()
    for _ in range(rng.randint(1, 3)):
        cont, key = rng.choice(f)
        q = parse_num(cont[key])
        if q is None: continue
        cont[key] = respell(q, rng, kinds)
    return 'respell_' + '+'.join(sorted(kinds)) if kinds else None


def m_permute(c, rng):
    lists = [r['body'] for r in c.cons + c.ders if r['body'] != 'OBJ' and len(r['body']) > 1]
    lists += [d['reason'][1] for d in c.ders if d['reason'][0] in ('lin', 'rnd') and len(d['reason'][1]) > 1]
    lists += [s[1] for s in c.sols if len(s[1]) > 1]
    if not lists: return None
    rng.shuffle(rng.choice(lists))
    return 'permute'


def m_rename(c, rng):
    r = rng.choice(c.cons + c.ders)
    r['name'] = r['name'] + '_r' + str(rng.randint(0, 99))
    return 'rename'


def m_zero_term(c, rng):
    rows = [r for r in c.cons + c.ders if r['body'] != 'OBJ']
    if not rows: return None
    r = rng.choice(rows)
    used = {int(i) for i, _ in r['body']}
    free = [j for j in range(len(c.vars)) if j not in used]
    if not free: return None
    r['body'].append([str(rng.choice(free)), '0'])
    return 'zero_term'


PRESERVING = [m_respell, m_permute, m_rename, m_zero_term]


def m_multiplier(c, rng):
    ds = [d for d in c.ders if d['reason'][0] in ('lin', 'rnd') and d['reason'][1]]
    if not ds: return None
    p = rng.choice(rng.choice(ds)['reason'][1])
    q = parse_num(p[1])
    p[1] = canon(rng.choice([q * 2, q / 2, -q, q + Q(1, 7), Q(0), q * Q(3, 2)]))
    return 'multiplier'


def m_rhs(c, rng):
    r = rng.choice(c.cons + c.ders)
    q = parse_num(r['rhs'])
    r['rhs'] = canon(q + rng.choice([Q(1), Q(-1), Q(1, 3), Q(-1, 2), Q(1, 1000)]))
    return 'rhs_' + ('con' if r in c.cons else 'der')


def m_sense(c, rng):
    r = rng.choice(c.cons + c.ders)
    r['sense'] = rng.choice([s for s in 'ELG' if s != r['sense']])
    return 'sense_' + ('con' if r in c.cons else 'der')


def m_reason_kind(c, rng):
    ds = [d for d in c.ders if d['reason'][0] in ('lin', 'rnd')]
    if not ds: return None
    d = rng.choice(ds)
    d['reason'][0] = 'rnd' if d['reason'][0] == 'lin' else 'lin'
    return 'reason_kind'


def m_ref_index(c, rng):
    ds = [(k, d) for k, d in enumerate(c.ders) if d['reason'][0] in ('lin', 'rnd', 'uns') ]
    if not ds: return None
    k, d = rng.choice(ds)
    me = len(c.cons) + k
    new = str(rng.choice([me, me + 1, me - 1, -1, 2 ** 31 - 1, 2 ** 31, 2 ** 32 + 1, 0]))
    if d['reason'][0] == 'uns':
        d['reason'][rng.randint(1, 4)] = new
    elif d['reason'][1]:
        rng.choice(d['reason'][1])[0] = new
    else:
        return None
    return 'ref_index'


def m_coeff(c, rng):
    rows = [r for r in c.cons + c.ders if r['body'] != 'OBJ' and r['body']]
    if not rows: return None
    r = rng.choice(rows)
    p = rng.choice(r['body'])
    if rng.random() < 0.5:
        p[1] = canon(parse_num(p[1]) + rng.choice([Q(1), Q(-1), Q(1, 2)]))
        return 'coeff_' + ('con' if r in c.cons else 'der')
    p[0] = str(rng.choice([len(c.vars), -1, 2 ** 31, int(p[0]) + 1]))
    return 'var_index'


def m_int(c, rng):
    n = len(c.vars)
    if c.ints and rng.random() < 0.5:
        c.ints.remove(rng.choice(c.ints)); return 'int_remove'
    cand = [str(j) for j in range(n) if str(j) not in c.ints]
    if cand and rng.random() < 0.7:
        c.ints.append(rng.choice(cand)); return 'int_add'
    if c.ints:
        c.ints.append(c.ints[0]); return 'int_duplicate'
    return None


def m_rtp(c, rng):
    if c.rtp[0] == 'infeas':
        c.rtp[:] = ['range', rng.choice(['-inf', '0', '1']), rng.choice(['inf', '0', '1'])]
        return 'rtp_to_range'
    k = rng.choice([1, 2])
    choice = rng.random()
    if choice < 0.3:
        c.rtp[:] = ['infeas']; return 'rtp_to_infeas'
    if choice < 0.5:
        c.rtp[k] = 'inf' if k == 1 else '-inf'; return 'rtp_wrong_inf'
    v = c.rtp[k]
    q = parse_num(v) if v not in ('inf', '-inf') else Q(0)
    c.rtp[k] = canon(q + rng.choice([Q(1), Q(-1), Q(1, 2), Q(-1, 1000)]))
    return 'rtp_bound'


def m_sol(c, rng):
    if not c.sols:
        c.sols.append(['s_new', [[str(rng.randrange(len(c.vars))), str(rng.randint(-2, 2))]]])
        return 'sol_add'
    s = rng.choice(c.sols)
    r = rng.random()
    if r < 0.4 and s[1]:
        p = rng.choice(s[1]); p[1] = canon(parse_num(p[1]) + rng.choice([Q(1), Q(-1), Q(1, 2)]))
        return 'sol_value'
    if r < 0.6 and s[1]:
        s[1].append(list(s[1][0])); return 'sol_duplicate_index'
    if r < 0.8:
        s[1].append([str(len(c.vars)), '1']); return 'sol_index_oob'
    c.sols.remove(s); return 'sol_remove'


def m_objsense(c, rng):
    c.objsense = {'min': 'max', 'max': 'min'}.get(c.objsense, 'min')
    return 'objsense'


def m_uns(c, rng):
    ds = [d for d in c.ders if d['reason'][0] == 'uns']
    if not ds: return None
    r = rng.choice(ds)['reason']
    if rng.random() < 0.5:
        r[2], r[4] = r[4], r[2]; return 'uns_swap_asm'
    r[1], r[3] = r[3], r[1]; return 'uns_swap_branch'


def m_final_use(c, rng):
    if not c.ders: return None
    d = rng.choice(c.ders)
    me = len(c.cons) + c.ders.index(d)
    d['idx'] = str(rng.choice([me, me + 1, -1, 0]))
    return 'final_use_idx'


def m_drop_der(c, rng):
    if len(c.ders) < 2: return None
    k = rng.randrange(len(c.ders) - 1)
    c.ders.insert(k + 1, json.loads(json.dumps(c.ders[k])))
    return 'duplicate_der'


def m_sol_row(c, rng):
    """Edit an existing `{ sol }` row, or insert one just before the final row."""
    sols = [d for d in c.ders if d['reason'][0] == 'sol']
    if sols and rng.random() < 0.6:
        d = rng.choice(sols)
        if rng.random() < 0.5:
            d['sense'] = 'G' if d['sense'] == 'L' else 'L'; return 'sol_row_sense'
        d['rhs'] = canon(parse_num(d['rhs']) + rng.choice([Q(-1), Q(1), Q(-1, 2)])); return 'sol_row_rhs'
    if not c.ders or not c.sols: return None
    best = None
    obj = {int(i): parse_num(v) for i, v in c.obj}
    for _, vals in c.sols:
        v = sum(obj.get(int(i), 0) * parse_num(x) for i, x in vals)
        best = v if best is None else (min(best, v) if c.objsense == 'min' else max(best, v))
    k = len(c.ders) - 1
    sense = rng.choice(['L', 'G'])
    rhs = best + rng.choice([Q(0), Q(-1), Q(1)])
    c.ders.insert(k, {'name': 'sol_ins', 'sense': sense, 'rhs': canon(rhs), 'body': 'OBJ',
                      'reason': ['sol'], 'idx': '-1'})
    return 'sol_row_insert'


INVALIDATING = [m_sol_row, m_multiplier, m_rhs, m_sense, m_reason_kind, m_ref_index, m_coeff, m_int,
                m_rtp, m_sol, m_objsense, m_uns, m_final_use, m_drop_der]

# ----------------------------------------------------------------------------------
# Running checkers

def classify(name, rc, out):
    if rc is None: return 'TIMEOUT'
    if rc < 0 or rc in (134, 136, 139): return 'CRASH'
    if name.startswith('lean'):
        return {0: 'ACCEPT', 1: 'PARSE', 2: 'REJECT'}.get(rc, f'RC{rc}')
    return 'ACCEPT' if rc == 0 else 'REJECT'


def run_checkers(checkers, path, timeout=30):
    res = {}
    for name, cmd in checkers:
        args = [a.replace('{}', path) for a in shlex.split(cmd)]
        try:
            p = subprocess.run(args, capture_output=True, text=True, timeout=timeout,
                               errors='replace')
            rc, out = p.returncode, p.stdout + p.stderr
        except subprocess.TimeoutExpired:
            rc, out = None, ''
        res[name] = (classify(name, rc, out), out[-600:])
    return res


def one_case(job):
    seed_path, seed_text, case_id, rngseed, checkers, outdir, baseline = job
    rng = random.Random(rngseed)
    c = Cert(seed_text)
    labels = []
    preserving = rng.random() < 0.35
    pool = PRESERVING if preserving else INVALIDATING
    for _ in range(rng.choice([1, 1, 1, 2, 3])):
        lab = rng.choice(pool)(c, rng)
        if lab: labels.append(lab)
    if not labels:
        return None
    text = c.render(comments=preserving and rng.random() < 0.3, rng=rng)
    path = os.path.join(outdir, 'cases', f'{case_id}.vipr')
    with open(path, 'w') as f: f.write(text)
    res = run_checkers(checkers, path)
    verdicts = {k: v[0] for k, v in res.items()}
    truth = claim_true(c, ground_truth(c)) if len(c.vars) <= 12 else None
    return {'id': case_id, 'seed': os.path.basename(seed_path), 'labels': labels,
            'preserving': preserving, 'verdicts': verdicts, 'truth': truth,
            'outputs': {k: v[1] for k, v in res.items()}, 'baseline': baseline}


def interesting(r):
    v = r['verdicts']
    vals = set(v.values())
    reasons = []
    if 'CRASH' in vals or 'TIMEOUT' in vals: reasons.append('crash_or_timeout')
    if r['truth'] is False and 'ACCEPT' in vals:
        reasons.append('ACCEPTS_FALSE_CLAIM:' + ','.join(k for k, x in v.items() if x == 'ACCEPT'))
    acc = {k: x == 'ACCEPT' for k, x in v.items()}
    if len(set(acc.values())) > 1: reasons.append('disagree')
    if r['preserving']:
        for k, x in v.items():
            if (x == 'ACCEPT') != (r['baseline'][k] == 'ACCEPT'):
                reasons.append('preserving_changed:' + k)
    return reasons


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--checker', action='append', required=True, help='NAME=CMD with {} for path')
    ap.add_argument('--seeds', nargs='+', required=True)
    ap.add_argument('--cases', type=int, default=1000)
    ap.add_argument('--jobs', type=int, default=os.cpu_count())
    ap.add_argument('--out', default='difftest-out')
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    checkers = [tuple(c.split('=', 1)) for c in a.checker]
    os.makedirs(os.path.join(a.out, 'cases'), exist_ok=True)
    seeds = []
    for s in a.seeds:
        text = open(s).read()
        try:
            Cert(text)
        except Exception as e:
            print(f'skip seed {s}: {e}', file=sys.stderr); continue
        base = {k: v[0] for k, v in run_checkers(checkers, s).items()}
        print(f'seed {os.path.basename(s)}: {base}')
        seeds.append((s, text, base))
    rng = random.Random(a.seed)
    jobs = []
    for i in range(a.cases):
        s, text, base = rng.choice(seeds)
        jobs.append((s, text, i, rng.randrange(2 ** 62), checkers, a.out, base))
    results = []
    with ProcessPoolExecutor(a.jobs) as ex:
        for r in ex.map(one_case, jobs, chunksize=4):
            if r: results.append(r)
    with open(os.path.join(a.out, 'results.jsonl'), 'w') as f:
        for r in results:
            r['interesting'] = interesting(r)
            f.write(json.dumps(r) + '\n')
    found = [r for r in results if r['interesting']]
    print(f'{len(results)} cases, {len(found)} interesting')
    from collections import Counter
    sig = Counter()
    for r in found:
        key = (tuple(sorted(set(x.split(':')[0] + (':' + x.split(':')[1] if ':' in x else '') for x in r['interesting']))),
               tuple(sorted(r['verdicts'].items())), tuple(r['labels']))
        sig[key] += 1
    for (why, verd, labels), n in sig.most_common(60):
        print(f'{n:5}  {list(why)}  {dict(verd)}  {list(labels)}')


if __name__ == '__main__':
    main()
