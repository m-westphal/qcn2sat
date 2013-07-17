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

from qcsp2sat import PropositionalAtoms

def check_allen_signature(signature):
    if signature != frozenset([ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di', 'm', 'mi', 'o', 'oi' ]):
        raise SystemExit('Given signature does not match allen signature')

def instantiate(l, x, y, atoms): # encode instantiated literal l on x,y
    mod = 1
    if not l[0]:  # negated predicate
        mod = -1

    if l[1].relation == '=':  # for "=" we enforce symmetry
        if y < x or (y == x and l[1].var1[1] == '+' and l[1].var2[1] == '-'):
#            print "Wrap", l[1].string, "for", x, y, ":",
            rel_string = l[1].swap_variables_string()
            rel_string = rel_string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
#            print rel_string
            return mod * atoms.encode(y,x, rel_string)

    rel_string = l[1].string.replace('x', str(x))
    rel_string = rel_string.replace('y', str(y))

    if x < y:
        return mod * atoms.encode(x, y, rel_string)
    # PropositionalAtoms::encode() assumes a <= b
    # ugly not wrapped URG
    return mod * atoms.encode(y, x, rel_string)

def nebel_buerckert_encode_variables(qcn, instance):
    check_allen_signature(qcn.signature)

    import os.path
    import itertools
    from syntactic_map import read_map
    syntactic_interpretation = read_map(os.path.join('data', 'ia_ordclauses.map'))

    atoms = PropositionalAtoms()

    boolvars = dict()
    used_points = set()
    for i, j in qcn.iterate_strict_triangle():
        r = qcn.get(i, j)

        for clause in syntactic_interpretation[frozenset(r)]:
            cl = [ ]
            for l in clause:
                cl.append( instantiate(l, i, j, atoms) )

                if 'x+' in l[1].string:
                    used_points.add( (i,'+') )
                else:
                    used_points.add( (i,'-') )
                if 'y+' in l[1].string:
                    used_points.add( (j,'+') )
                else:
                    used_points.add( (j,'-') )
            instance.add_clause( cl )

    from syntactic_map import predicate
    # encode ORD theory
    for i, s in used_points:
        # domain formula
        if s == '-' and (i, '+') in used_points:
            instance.add_clause([ instantiate((True, predicate(None, 'x-', '<=', 'x+')), i, i, atoms) ])
            instance.add_clause([ instantiate((False, predicate(None, 'x-', '=', 'x+')), i, i, atoms) ])
        continue

    for p1, s1 in used_points:
        for p2, s2 in used_points:
            if (p1,s1) == (p2,s2):
                continue

            if (not p1 == p2) and qcn.graph and (p1, p2) not in qcn.graph:
                continue

            # (3.) x <= y ^ y <= x -> x = y
            if p1 < p2 or (p1 == p2 and s1 < s2):
                instance.add_clause([ instantiate( (False, predicate(None, 'x'+s1, '<=', 'y'+s2)), p1, p2, atoms),
                    instantiate( (False, predicate(None, 'x'+s2, '<=', 'y'+s1)), p2, p1, atoms),
                    instantiate( (True, predicate(None, 'x'+s1, '=', 'y'+s2)), p1, p2, atoms) ])

            # (4.) (5.) x = y -> x <= y
            instance.add_clause([ instantiate( (False, predicate(None, 'x'+s1, '=', 'y'+s2)), p1, p2, atoms),
                instantiate( (True, predicate(None, 'x'+s1, '<=', 'y'+s2)), p1, p2, atoms) ])
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
                instance.add_clause([ instantiate( (False, predicate(None, 'x'+s1, '<=', 'y'+s2)), p1, p2, atoms),
                    instantiate( (False, predicate(None, 'x'+s2, '<=', 'y'+s3)), p2, p3, atoms),
                    instantiate( (True, predicate(None, 'x'+s1, '<=', 'y'+s3)), p1, p3, atoms) ])


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
