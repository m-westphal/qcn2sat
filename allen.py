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

from qcsp2sat import PropositionalAtoms

def check_allen_signature(signature):
    if signature != frozenset([ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di', 'm', 'mi', 'o', 'oi' ]):
        raise SystemExit('Given signature does not match allen signature')

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

def instantiate(l, x, y, atoms): # encode instantiated literal l on x,y
    assert l.x == 'x' or (l.x == l.y == 'y')
    assert l.y in ['x', 'y']
    (s1,s2,rel) = (l.s1, l.s2, l.r)

    assert rel in [ '<=', '=', '>=' ]

    m = 1
    if not l.is_positive():
        m = -1

    a = x
    if l.x == 'y':
        a = y
    b = y
    if l.y == 'x':
        b = x

    # PropositionalAtoms::encode() assumes a <= b: which is not true in our
    # case, so we secretly wrap the *identification string*
    # For "=" we assume symmetry
    if a < b or (a == b and s1 < s2):
        return m * atoms.encode(a, b, rel+s1+s2)
    else: # swap
        srel = None
        if rel == '<=':
            srel = '>='
        elif rel == '=':
            srel = '='
        elif rel == '>=':
            srel = '<='
        assert srel
        return m * atoms.encode(b,a,srel+s2+s1)

def nebel_buerckert_encode_variables(qcn, instance):
    check_allen_signature(qcn.signature)

    import os.path
    import itertools
    syntactic_interpretation = read_map(qcn.signature, os.path.join('data', 'ia_ordclauses.map'))

    atoms = PropositionalAtoms()

    boolvars = dict()
    used_points = set()
    for i, j in qcn.iterate_strict_triangle():
        r = qcn.get(i, j)

        for clause in syntactic_interpretation[frozenset(r)]:
            cl = [ ]
            for l in clause:
                cl.append( instantiate(l, i, j, atoms) )
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
        # well-formed intervals
        if s == '-' and (i, '+') in used_points:
            instance.add_clause([ instantiate( literal('p', 'x', '-', '<=', 'x', '+'), i, i, atoms) ])
            instance.add_clause([ instantiate( literal('n', 'x', '-', '=', 'x', '+'), i, i, atoms) ])
        continue

    for p1, s1 in used_points:
        for p2, s2 in used_points:
            if (p1,s1) == (p2,s2):
                continue

            if (not p1 == p2) and qcn.graph and (p1, p2) not in qcn.graph:
                continue

            # (3.) x <= y ^ y <= x -> x = y
            if p1 < p2 or (p1 == p2 and s1 < s2):
                instance.add_clause([ instantiate( literal('n', 'x', s1, '<=', 'y', s2), p1, p2, atoms),
                    instantiate( literal('n', 'x', s2, '<=', 'y', s1), p2, p1, atoms),
                    instantiate( literal('p', 'x', s1, '=', 'y', s2), p1, p2, atoms) ])

            # (4.) (5.) x = y -> x <= y
            instance.add_clause([ instantiate( literal('n', 'x', s1, '=', 'y', s2), p1, p2, atoms),
                instantiate( literal('p', 'x', s1, '<=', 'y', s2), p1, p2, atoms) ])
    for p1, s1 in used_points:
        for p2, s2 in used_points:

            if (not p1 == p2) and qcn.graph and (p1, p2) not in qcn.graph:
                continue

            if (p1,s1) == (p2,s2):
                continue

            for p3, s3 in used_points:

                if (not p1 == p3) and qcn.graph and (p1, p3) not in qcn.graph:
                    continue

                if (not p2 == p3) and qcn.graph and (p2, p3) not in qcn.graph:
                    continue

                if (p1,s1) == (p3,s3) or (p2,s2) == (p3,s3):
                    continue

                # (1.) x <= y ^ y <= z -> x <= z
                instance.add_clause([ instantiate( literal('n', 'x', s1, '<=', 'y', s2), p1, p2, atoms),
                    instantiate( literal('n', 'x', s2, '<=', 'y', s3), p2, p3, atoms),
                    instantiate( literal('p', 'x', s1, '<=', 'y', s3), p1, p3, atoms) ])


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

def pham_mu(br):
    if br == '=':
        return ['=--', '<-+', '>+-', '=++']
    elif br == '<':
        return ['<--', '<-+', '<+-', '<++']
    elif br == '>':
        return ['>--', '>-+', '>+-', '>++']
    elif br == 'd':
        return ['>--', '<-+', '>+-', '<++']
    elif br == 'di':
        return ['<--', '<-+', '>+-', '>++']
    elif br == 'o':
        return ['<--', '<-+', '>+-', '<++']
    elif br == 'oi':
        return ['>--', '<-+', '>+-', '>++']
    elif br == 'm':
        return ['<--', '<-+', '=+-', '<++']
    elif br == 'mi':
        return ['>--', '=-+', '>+-', '>++']
    elif br == 's':
        return ['=--', '<-+', '>+-', '<++']
    elif br == 'si':
        return ['=--', '<-+', '>+-', '>++']
    elif br == 'f':
        return ['>--', '<-+', '>+-', '=++']
    elif br == 'fi':
        return ['<--', '<-+', '>+-', '=++']
    assert False


def get_pa_min_excl_clause(x, y, br, atoms):
    if br == '<':
        return [ -1 * atoms.encode(x,y,'<+-') ]
    elif br == '>':
        return [ -1 * atoms.encode(x,y,'>-+') ]
    elif br == '=':
        return [ -1 * atoms.encode(x,y,'=--'),
                 -1 * atoms.encode(x,y,'=++') ]
    elif br == 'd':
        return [ -1 * atoms.encode(x,y,'>--'),
                 -1 * atoms.encode(x,y,'<++') ]
    elif br == 'di':
        return [ -1 * atoms.encode(x,y,'<--'),
                 -1 * atoms.encode(x,y,'>++') ]
    elif br == 'o':
        return [ -1 * atoms.encode(x,y,'<--'),
                 -1 * atoms.encode(x,y,'<++'),
                 -1 * atoms.encode(x,y,'>+-') ]
    elif br == 'oi':
        return [ -1 * atoms.encode(x,y,'>--'),
                 -1 * atoms.encode(x,y,'>++'),
                 -1 * atoms.encode(x,y,'<-+') ]
    elif br == 'm':
        return [ -1 * atoms.encode(x,y,'=+-') ]
    elif br == 'mi':
        return [ -1 * atoms.encode(x,y,'=-+') ]
    elif br == 's':
        return [ -1 * atoms.encode(x,y,'=--'),
                 -1 * atoms.encode(x,y,'<++') ]
    elif br == 'si':
        return [ -1 * atoms.encode(x,y,'=--'),
                 -1 * atoms.encode(x,y,'>++') ]
    elif br == 'f':
        return [ -1 * atoms.encode(x,y,'>--'),
                 -1 * atoms.encode(x,y,'=++') ]
    elif br == 'fi':
        return [ -1 * atoms.encode(x,y,'<--'),
                 -1 * atoms.encode(x,y,'=++') ]
    assert False

def pham_pt_directDomEncoding(qcn, out, atoms):
    # encode domains

    pa_network = dict()

    for i, j in qcn.iterate_strict_triangle():
        rel_ij = qcn.get(i, j)
        pa_set = set()
        for br in rel_ij:
            pa_set |= set(pham_mu(br))
        try:
            pa_network[i][j] = frozenset(pa_set)
        except KeyError:
            new = dict()
            new[j] = frozenset(pa_set)
            pa_network[i] = new

        for s1 in ['-', '+']:
            for s2 in ['-', '+']:
                assert i != j

                alo = [ ]
                for p in [ '<'+s1+s2, '='+s1+s2, '>'+s1+s2 ]:
                    if p in pa_set:
                        alo.append(atoms.encode(i,j,p))
                assert alo
                out.add_clause(alo)

                if '<'+s1+s2 in pa_set and '='+s1+s2 in pa_set:
                    amo = [ -1 * atoms.encode(i,j,'<'+s1+s2),
                            -1 * atoms.encode(i,j,'='+s1+s2) ]
                    out.add_clause(amo)
                if '<'+s1+s2 in pa_set and '>'+s1+s2 in pa_set:
                    amo = [ -1 * atoms.encode(i,j,'<'+s1+s2),
                            -1 * atoms.encode(i,j,'>'+s1+s2) ]
                    out.add_clause(amo)
                if '='+s1+s2 in pa_set and '>'+s1+s2 in pa_set:
                    amo = [ -1 * atoms.encode(i,j,'='+s1+s2),
                            -1 * atoms.encode(i,j,'>'+s1+s2) ]
                    out.add_clause(amo)

    # encode input
    done_intervals = set()
    for i, j in qcn.iterate_strict_triangle():
        for t in [i, j]:
            if not t in done_intervals:
                # well formed intervals
                wf = [ atoms.encode(t,t,'>+-') ]
                try:
                    pa_network[t][t] = frozenset(['>+-'])
                except KeyError:
                    new = dict()
                    new[t] = frozenset(['>+-'])
                    pa_network[t] = new
                out.add_clause(wf)
                done_intervals.add(t)

        # (FOR) clauses
        exclude = list(qcn.signature - frozenset(qcn.get(i,j)))
        exclude.sort()
        pa_set = pa_network[i][j]
        for br in exclude:
            req = True
            for mu_br in pham_mu(br):
                if not mu_br in pa_set: # CHANGED NOT
                    req = False
                    break
            if req or True:
                clause = []
                for mu_br in pham_mu(br):
                    clause += [ -1 * atoms.encode(i,j,mu_br) ]
                out.add_clause(clause)
    return pa_network

def pham_support_pt_encode(qcn, instance):
    check_allen_signature(qcn.signature)

    pa_comp = point_algebra_comptable()
    atoms = PropositionalAtoms()
    pa_network = pham_pt_directDomEncoding(qcn, instance, atoms)

    # encode PA theory
    for i in xrange(0, qcn.size):
        for j in xrange(i, qcn.size):
            for k in xrange(j, qcn.size):
                for s1 in ['-', '+']:
                    for s2 in ['-', '+']:
                        if i == j and s1 >= s2:
                            continue
                        if i != j and qcn.graph and (i,j) not in qcn.graph:
                            continue
                        for s3 in ['-', '+']:
                            if (i == k and s1 >= s3) or (j == k and s2 >= s3):
                                continue
                            if i != k and qcn.graph and (i,k) not in qcn.graph:
                                continue
                            if j != k and qcn.graph and (j,k) not in qcn.graph:
                                continue

                            for br1 in ['<', '=', '>']:
                                if br1+s1+s2 not in pa_network[i][j]:
                                    continue
                                b_ij = atoms.encode(i,j,br1+s1+s2)
                                for br2 in ['<', '=', '>']:
                                    if br2+s2+s3 not in pa_network[j][k]:
                                        continue
                                    support = list(pa_comp[br1+" "+br2])
                                    support.sort()
                                    b_jk= atoms.encode(j,k,br2+s2+s3)
                                    cl = [ -1 * b_ij, -1 * b_jk ]
                                    for br in support:
                                        if br+s1+s3 in pa_network[i][k]:
                                            cl += [ atoms.encode(i,k,br+s1+s3) ]
                                    instance.add_clause(cl)

def pham_direct_pt_encode(qcn, instance):
    check_allen_signature(qcn.signature)

    pa_comp = point_algebra_comptable()
    atoms = PropositionalAtoms()
    pa_network = pham_pt_directDomEncoding(qcn, instance, atoms)

    # encode PA theory (direct)
    for i in xrange(0, qcn.size):
        for j in xrange(i, qcn.size):
            for k in xrange(j, qcn.size):
                for s1 in ['-', '+']:
                    for s2 in ['-', '+']:
                        if i == j and s1 >= s2:
                            continue
                        if i != j and qcn.graph and (i,j) not in qcn.graph:
                            continue
                        for s3 in ['-', '+']:
                            if (i == k and s1 >= s3) or (j == k and s2 >= s3):
                                continue
                            if i != k and qcn.graph and (i,k) not in qcn.graph:
                                continue
                            if j != k and qcn.graph and (j,k) not in qcn.graph:
                                continue

                            for br1 in ['<', '=', '>']:
                                if br1+s1+s2 not in pa_network[i][j]:
                                    continue
                                b_ij = atoms.encode(i,j,br1+s1+s2)
                                for br2 in ['<', '=', '>']:
                                    if br2+s2+s3 not in pa_network[j][k]:
                                        continue

                                    b_jk= atoms.encode(j,k,br2+s2+s3)

                                    rule_out = list(qcn.signature - pa_comp[br1+" "+br2])
                                    rule_out.sort()
                                    for br in rule_out:
                                        if br+s1+s3 in pa_network[i][k]:
                                            cl = [ -1 * b_ij, -1 * b_jk ] \
                                                + [ -1 * atoms.encode(i,k,br+s1+s3) ]
                                            instance.add_clause(cl)
