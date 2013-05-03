#! /usr/bin/env python
# -*- coding: UTF-8 -*-

# ex: set tabstop=4 expandtab softtabstop=4:

# qcsp2sat.py: convert qualitative CSPs to CNF formulae
# Copyright (C) 2009-2011  Matthias Westphal
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

from ordclauses import literal

def encodeDict(x, s1, y, s2, baserel, d):   # assign a boolean variable id to baserel in R_ij
    i = str(x)+s1
    j = str(y)+s2
    try:
        return d[i][j][baserel]
    except KeyError:
        assert x <= y
        try:
            d["max"] += 1
        except KeyError:
            d["max"] = 1

        ret = d["max"]
        if not i in d:
            d[i] = dict()
        if not j in d[i]:
            d[i][j] = dict()
        assert not baserel in d[i][j]
        d[i][j][baserel] = ret
        return ret

def parse_cnf_string(s):
    import re

    clause_regexp = re.compile(r'^{ ([^}]+) }(.*)')

    assert s == s.strip()

    clauses = [ ]
    while s:
        cl = re.match(clause_regexp, s)
        assert cl
        clauses.append(cl.group(1).strip())
        s = cl.group(2).strip()

    lit_regexp = re.compile(r'^([+-])\(([xy])([+-]) ([<=>][<=>]) ([xy])([+-])\)(.*)')

    cnf = set()
    for c in clauses:
        clause = set()
        while c:
            m = re.match(lit_regexp, c)
            assert m
            c = m.group(7).strip()

            clause.add( literal(m.group(1), m.group(2), m.group(3), m.group(4), m.group(5), m.group(6)) )
        cnf.add( frozenset(clause) )

    return cnf

def read_map(signature, filename):
    import re

    m = dict()

    f = open(filename, 'r')

    regexp = re.compile(r'^x \((.*)\) y :: {(.*)}$')

    for l in f:
        match = re.match(regexp, l)
        if match:
            s = match.group(1)
            relation = frozenset(s.strip().split(' '))
            assert not relation in m
            for b in relation:
                if not b in signature:
                    raise SystemExit("ORD-horn map does not match given signature of calculus")

            s = match.group(2).strip()

            cnf = parse_cnf_string(s)
#            cnf = ?

            m[relation] = cnf
        else:
            raise SystemExit("Failed to parse syntactic interpretations in '%s', line '%s'" % (filename, l))

    assert len(m) >= 2^13-1

    return m

def instantiate(l, x, y, d): # encode instantiated literal l on x,y
    assert l.x == 'x' or (l.x == l.y == 'y')
    assert l.y in ['x', 'y']
    (s1,s2,rel) = (l.s1, l.s2, l.r)

    m = 1
    if not l.is_positive():
        m = -1

    a = x
    if l.x == 'y':
        a = y
    b = y
    if l.y == 'x':
        b = x

    if a <= b:
        return m * encodeDict(a, s1, b,s2, rel, d)
    else: # swap
        srel = '<='
        if rel == '<=':
            srel = '>='
        elif rel == '=':
            srel = '='
        else:
            assert rel == '>='
        return m * encodeDict(b, s2, a, s1, srel, d)

def nebel_buerckert_encode_variables(signature, instance, CSP, max_node, boolvars):
    import os.path
    import itertools
    syntactic_interpretation = read_map(signature, os.path.join('data', 'ordclauses.map'))

    used_points = set()
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r = CSP[i][j]

            for clause in syntactic_interpretation[frozenset(r)]:
                cl = [ ]
                for l in clause:
                    cl.append( instantiate(l, i, j, boolvars) )
                    if l.x == 'x':
                        used_points.add( (i,l.s1) )
                    else:
                        used_points.add( (j,l.s1) )
                    if l.y == 'x':
                        used_points.add( (i,l.s2) )
                    else:
                        used_points.add( (j,l.s2) )
                instance.add_clause( cl )

    # encode ORD theory
    for i, s in used_points:
        # (2.) x <= x
        instance.add_clause([ instantiate( literal('p', 'x', s, '<=', 'x', s), i, i, boolvars) ])

        if s == '-' and (i, '+') in used_points:
            # well-formed intervals
            instance.add_clause([ instantiate( literal('p', 'x', '-', '<=', 'x', '+'), i, i, boolvars) ])
            instance.add_clause([ instantiate( literal('n', 'x', '-', '=', 'x', '+'), i, i, boolvars) ])
        continue

    for p1, s1 in used_points:
        for p2, s2 in used_points:
            if (p1,s1) == (p2,s2):
                continue
            if p1 <= p2:
                # (3.) x <= y ^ y <= x -> x = y
                instance.add_clause([ instantiate( literal('n', 'x', s1, '<=', 'y', s2), p1, p2, boolvars),
                    instantiate( literal('n', 'x', s2, '<=', 'y', s1), p2, p1, boolvars),
                    instantiate( literal('p', 'x', s1, '=', 'y', s2), p1, p2, boolvars) ])

            # (4.) (5.) x = y -> x <= y
            instance.add_clause([ instantiate( literal('n', 'x', s1, '=', 'y', s2), p1, p2, boolvars),
                instantiate( literal('p', 'x', s1, '<=', 'y', s2), p1, p2, boolvars) ])
    for p1, s1 in used_points:
        for p2, s2 in used_points:
            for p3, s3 in used_points:
                if (p1,s1) == (p2,s2) or (p1,s1) == (p3,s3) or (p2,s2) == (p3,s3):
                    continue

                # (1.) x <= y ^ y <= z -> x <= z
                instance.add_clause([ instantiate( literal('n', 'x', s1, '<=', 'y', s2), p1, p2, boolvars),
                    instantiate( literal('n', 'x', s2, '<=', 'y', s3), p2, p3, boolvars),
                    instantiate( literal('p', 'x', s1, '<=', 'y', s3), p1, p3, boolvars) ])


def point_algebra_comptable():
    pa = dict()
    pa["< <"] = frozenset( [ '<' ] )
    pa["< ="] = frozenset( [ '<' ] )
    pa["< >"] = frozenset( [ '<', '=', '>' ] )
    pa["= <"] = frozenset( [ '<' ] )
    pa["= ="] = frozenset( [ '=' ] )
    pa["= >"] = frozenset( [ '>' ] )
    pa["> <"] = frozenset( [ '<', '=', '>' ] )
    pa["> ="] = frozenset( [ '>' ] )
    pa["> >"] = frozenset( [ '>' ] )

    return pa

def get_pa_excl_clause(x, y, br, d):
    if br == '<':
        return [ -1 * encodeDict(x,'+', y,'-', '<', d) ]
    elif br == '>':
        return [ -1 * encodeDict(x,'-', y,'+', '>', d) ]
    elif br == '=':
        return [ -1 * encodeDict(x,'-', y,'-', '=', d),
                 -1 * encodeDict(x,'+', y,'+', '=', d) ]
    elif br == 'd':
        return [ -1 * encodeDict(x,'-', y,'-', '>', d),
                 -1 * encodeDict(x,'+', y,'+', '<', d) ]
    elif br == 'di':
        return [ -1 * encodeDict(x,'-', y,'-', '<', d),
                 -1 * encodeDict(x,'+', y,'+', '>', d) ]
    elif br == 'o':
        return [ -1 * encodeDict(x,'-', y,'-', '<', d),
                 -1 * encodeDict(x,'+', y,'+', '<', d),
                 -1 * encodeDict(x,'+', y,'-', '>', d) ]
    elif br == 'oi':
        return [ -1 * encodeDict(x,'-', y,'-', '>', d),
                 -1 * encodeDict(x,'+', y,'+', '>', d),
                 -1 * encodeDict(x,'-', y,'+', '<', d) ]
    elif br == 'm':
        return [ -1 * encodeDict(x,'+', y,'-', '=', d) ]
    elif br == 'mi':
        return [ -1 * encodeDict(x,'-', y,'+', '=', d) ]
    elif br == 's':
        return [ -1 * encodeDict(x,'-', y,'-', '=', d),
                 -1 * encodeDict(x,'+', y,'+', '<', d) ]
    elif br == 'si':
        return [ -1 * encodeDict(x,'-', y,'-', '=', d),
                 -1 * encodeDict(x,'+', y,'+', '>', d) ]
    elif br == 'f':
        return [ -1 * encodeDict(x,'-', y,'-', '>', d),
                 -1 * encodeDict(x,'+', y,'+', '=', d) ]
    elif br == 'fi':
        return [ -1 * encodeDict(x,'-', y,'-', '<', d),
                 -1 * encodeDict(x,'+', y,'+', '=', d) ]
    assert False

def pham_support_pt_encode(signature, instance, CSP, max_node, cgraph):
#    if frozenset(signature) != frozenset([ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di', 'm', 'mi', 'o', 'oi' ]):
#        raise SystemExit('Given signature does not match allen signature')

    d = dict()
    pa_comp = point_algebra_comptable()
    import os.path

    # encode domains
    for i in xrange(max_node+1):
        for j in xrange(i, max_node+1):
            if not (i,j) in cgraph:
                continue
            for s1 in ['-', '+']:
                for s2 in ['-', '+']:
                    if (i,s1) == (j,s2):
                        continue
                    alo = [ encodeDict(i, s1, j, s2, '<', d),
                            encodeDict(i, s1, j, s2, '=', d),
                            encodeDict(i, s1, j, s2, '>', d) ]
                    instance.add_clause(alo)

                    amo = [ -1 * encodeDict(i, s1, j, s2, '<', d),
                            -1 * encodeDict(i, s1, j, s2, '=', d) ]
                    instance.add_clause(amo)
                    amo = [ -1 * encodeDict(i, s1, j, s2, '<', d),
                            -1 * encodeDict(i, s1, j, s2, '>', d) ]
                    instance.add_clause(amo)
                    amo = [ -1 * encodeDict(i, s1, j, s2, '=', d),
                            -1 * encodeDict(i, s1, j, s2, '>', d) ]
                    instance.add_clause(amo)

    # encode input
    for i in xrange(max_node+1):
        # well formed intervals
        wf = [ encodeDict(i, '-', i, '+', '<', d) ]
        instance.add_clause(wf)

        for j in xrange(i+1, max_node+1):
            if not (i,j) in cgraph:
                continue
            exclude = signature - frozenset(CSP[i][j])
            for br in exclude:
                clause = get_pa_excl_clause(i, j, br, d)
                instance.add_clause(clause)
    # encode PA theory
    for i in xrange(max_node+1):
        for j in xrange(i, max_node+1):
            if not (i,j) in cgraph:
                continue
            for k in xrange(j, max_node+1):
                if not (i,k) in cgraph:
                    continue
                if not (j,k) in cgraph:
                    continue
                for s1 in ['-', '+']:
                    for s2 in ['-', '+']:
                        if (i,s1) == (j,s2):
                            continue
                        for s3 in ['-', '+']:
                            if (i,s1) == (k,s3):
                                continue
                            if (j,s2) == (k,s3):
                                continue
                            for br1 in ['<', '=', '>']:
                                b_ij = encodeDict(i,s1,j,s2, br1, d)
                                for br2 in ['<', '=', '>']:
                                    b_jk= encodeDict(j,s2,k,s3, br2, d)
                                    cl = [ -1 * b_ij, -1 * b_jk ] \
                                        + [ encodeDict(i,s1,k,s3, br, d) for br in pa_comp[br1+" "+br2] ]
                                    instance.add_clause(cl)
