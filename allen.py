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

def read_map(filename):
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

def nebel_buerckert_encode_variables(instance, CSP, max_node, boolvars):
    import os.path
    import itertools
    syntactic_interpretation = read_map(os.path.join('data', 'ordclauses.map'))

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
