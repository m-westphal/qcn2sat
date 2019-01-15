#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Allen specific functions."""

# ex: set tabstop=4 expandtab softtabstop=4:

# qcn2sat.py: convert qualitative constraint networks to propositional CNF
# Copyright (C) 2009-2014  Matthias Westphal
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

from __future__ import absolute_import
from six.moves import range
def check_allen_signature(signature):
    """Check if signature is Allen signature."""
    if signature != frozenset([ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di',
        'm', 'mi', 'o', 'oi' ]):
        raise SystemExit('Given signature does not match allen signature')

def instantiate(l, x, y, atoms): # pylint: disable=C0103
    """encode instantiated literal l on x,y"""

    mod = 1
    if not l[0]:  # negated predicate
        mod = -1

    if l[1].relation == '=':  # for "=" we enforce symmetry
        if y < x or (y == x and l[1].var1[1] == '+' and l[1].var2[1] == '-'):
            rel_string = l[1].swap_variables_string()
            rel_string = rel_string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
            return mod * atoms.encode(y, x, rel_string)

    rel_string = l[1].string.replace('x', str(x))
    rel_string = rel_string.replace('y', str(y))

    if x < y:
        return mod * atoms.encode(x, y, rel_string)
    # PropositionalAtoms::encode() assumes a <= b
    # The string is NOT rewritten ... It just gets filed under (y,x)
    return mod * atoms.encode(y, x, rel_string)


def ord_horn_encode_input(qcn, instance, atoms):
    """Encode instance according to ORD-Horn map (but not the ORD-theory)."""

    import os.path
    from syntactic_map import read_map
    syntactic_interpretation = \
        read_map(os.path.join('data', 'ia_ordclauses.map'))

    used_points = set()
    for i, j in qcn.iterate_strict_triangle():
        relation = qcn.get(i, j)

        for clause in syntactic_interpretation[frozenset(relation)]:
            new_clause = [ ]
            for l in clause:  # pylint: disable=C0103
                new_clause.append( instantiate(l, i, j, atoms) )

                if 'x+' in l[1].string:
                    used_points.add( (i,'+') )
                if 'x-' in l[1].string:
                    used_points.add( (i,'-') )
                if 'y+' in l[1].string:
                    used_points.add( (j,'+') )
                if 'y-' in l[1].string:
                    used_points.add( (j,'-') )
            instance.add_clause( new_clause )

    return used_points

def ord_horn_encode_variables(qcn, instance): # pylint: disable=R0912
    """Encode instance according to ORD-Horn map."""
    check_allen_signature(qcn.signature)

    from qcn2sat import PropositionalAtoms
    atoms = PropositionalAtoms()

    # encode input
    used_points = ord_horn_encode_input(qcn, instance, atoms)

    # encode ORD theory
    from syntactic_map import Predicate
    for i, s1 in used_points: # pylint: disable=C0103
        # domain formula
        if s1 == '-' and (i, '+') in used_points:
            instance.add_clause([ instantiate((True, Predicate(None,
                'x-', '<=', 'x+')), i, i, atoms) ])
            instance.add_clause([ instantiate((False, Predicate(None,
                'x-', '=', 'x+')), i, i, atoms) ])
        continue

    for i, s1 in used_points: # pylint: disable=C0103
        for j, s2 in used_points: # pylint: disable=C0103
            if (i, s1) == (j, s2):
                continue

            if (not i == j) and qcn.graph and (i, j) not in qcn.graph:
                continue

            # x <= y ^ y <= x -> x = y
            if i < j or (i == j and s1 < s2):
                # avoid generating the same clauses twice
                instance.add_clause([ instantiate( (False, Predicate(None,
                    'x'+s1, '<=', 'y'+s2)), i, j, atoms),
                    instantiate( (False, Predicate(None, 'x'+s2, '<=', 'y'+s1)),
                    j, i, atoms),
                    instantiate( (True, Predicate(None, 'x'+s1, '=', 'y'+s2)),
                    i, j, atoms) ])

            # x = y -> x <= y
            instance.add_clause([ instantiate( (False, Predicate(None,
                'x'+s1, '=', 'y'+s2)), i, j, atoms),
                instantiate( (True, Predicate(None, 'x'+s1, '<=', 'y'+s2)),
                i, j, atoms) ])
    for i, s1 in used_points:  # pylint: disable=C0103
        for j, s2 in used_points:  # pylint: disable=C0103
            if (not i == j) and qcn.graph and (i, j) not in qcn.graph:
                continue

            if (i, s1) == (j, s2):
                continue

            for k, s3 in used_points:  # pylint: disable=C0103
                if (not i == k) and qcn.graph and (i, k) not in qcn.graph:
                    continue

                if (not j == k) and qcn.graph and (j, k) not in qcn.graph:
                    continue

                if (i, s1) == (k, s3) or (j, s2) == (k, s3):
                    continue

                # x <= y ^ y <= z -> x <= z
                instance.add_clause([ instantiate( (False, Predicate(None,
                    'x'+s1, '<=', 'y'+s2)), i, j, atoms),
                    instantiate( (False, Predicate(None, 'x'+s2, '<=', 'y'+s3)),
                    j, k, atoms),
                    instantiate( (True, Predicate(None, 'x'+s1, '<=', 'y'+s3)),
                    i, k, atoms) ])

def point_algebra_comptable():
    """Return composition table of the point algebra."""

    point_algebra_ct = dict()
    point_algebra_ct["< <"] = frozenset( [ '<' ] )
    point_algebra_ct["< ="] = frozenset( [ '<' ] )
    point_algebra_ct["< >"] = frozenset( [ '<', '=', '>' ] )
    point_algebra_ct["= <"] = frozenset( [ '<' ] )
    point_algebra_ct["= ="] = frozenset( [ '=' ] )
    point_algebra_ct["= >"] = frozenset( [ '>' ] )
    point_algebra_ct["> <"] = frozenset( [ '<', '=', '>' ] )
    point_algebra_ct["> ="] = frozenset( [ '>' ] )
    point_algebra_ct["> >"] = frozenset( [ '>' ] )

    return point_algebra_ct

def pham_mu(base_relation):
    """The mu function defined by Pham et al."""

    mu_fct = {
        '=': ['=--', '<-+', '>+-', '=++'],
        '<': ['<--', '<-+', '<+-', '<++'],
        '>': ['>--', '>-+', '>+-', '>++'],
        'd': ['>--', '<-+', '>+-', '<++'],
        'di':['<--', '<-+', '>+-', '>++'],
        'o': ['<--', '<-+', '>+-', '<++'],
        'oi':['>--', '<-+', '>+-', '>++'],
        'm':['<--', '<-+', '=+-', '<++'],
        'mi':['>--', '=-+', '>+-', '>++'],
        's':['=--', '<-+', '>+-', '<++'],
        'si':['=--', '<-+', '>+-', '>++'],
        'f':['>--', '<-+', '>+-', '=++'],
        'fi':['<--', '<-+', '>+-', '=++']
    }
    return mu_fct[base_relation]

def pham_pt_directDomEnc(qcn, out, atoms):#pylint: disable=C0103,R0914,R0912
    """Encode domains as in Pham et al. for point-based"""

    pa_network = dict()

    for i, j in qcn.iterate_strict_triangle():
        rel_ij = qcn.get(i, j)
        pa_set = set()
        for base_relation in rel_ij:
            pa_set |= set(pham_mu(base_relation))
        try:
            pa_network[i][j] = frozenset(pa_set)
        except KeyError:
            new = dict()
            new[j] = frozenset(pa_set)
            pa_network[i] = new

        for s1 in ['-', '+']:  # pylint: disable=C0103
            for s2 in ['-', '+']:  # pylint: disable=C0103
                assert i != j

                alo = [ ]
                for p in [ # pylint: disable=C0103
                    '<'+s1+s2, '='+s1+s2, '>'+s1+s2 ]:
                    if p in pa_set:  # pylint: disable=C0103
                        alo.append(atoms.encode(i, j, p))
                assert alo
                out.add_clause(alo)

                if '<'+s1+s2 in pa_set and '='+s1+s2 in pa_set:
                    amo = [ -1 * atoms.encode(i, j, '<'+s1+s2),
                            -1 * atoms.encode(i, j, '='+s1+s2) ]
                    out.add_clause(amo)
                if '<'+s1+s2 in pa_set and '>'+s1+s2 in pa_set:
                    amo = [ -1 * atoms.encode(i, j, '<'+s1+s2),
                            -1 * atoms.encode(i, j, '>'+s1+s2) ]
                    out.add_clause(amo)
                if '='+s1+s2 in pa_set and '>'+s1+s2 in pa_set:
                    amo = [ -1 * atoms.encode(i, j, '='+s1+s2),
                            -1 * atoms.encode(i, j, '>'+s1+s2) ]
                    out.add_clause(amo)

    # encode input
    done_intervals = set()
    for i, j in qcn.iterate_strict_triangle():
        for t in [i, j]:  # # pylint: disable=C0103
            if not t in done_intervals:
                # well formed intervals
                wf = [ atoms.encode(t, t, '>+-') ]  # pylint: disable=C0103
                try:
                    pa_network[t][t] = frozenset(['>+-'])
                except KeyError:
                    new = dict()
                    new[t] = frozenset(['>+-'])
                    pa_network[t] = new
                out.add_clause(wf)
                done_intervals.add(t)

        # (FOR) clauses
        exclude = list(qcn.signature - frozenset(qcn.get(i, j)))
        exclude.sort()
        pa_set = pa_network[i][j]
        for base_relation in exclude:
            req = True
            for mu_br in pham_mu(base_relation):
                if not mu_br in pa_set: # CHANGED NOT
                    req = False
                    break
            if req or True:
                clause = []
                for mu_br in pham_mu(base_relation):
                    clause += [ -1 * atoms.encode(i, j, mu_br) ]
                out.add_clause(clause)
    return pa_network

def pham_support_pt_encode(qcn, instance): # pylint: disable=R0914,R0912
    """The support encoding by Pham et al. for point-based"""

    check_allen_signature(qcn.signature)

    pa_comp = point_algebra_comptable()

    from qcn2sat import PropositionalAtoms
    atoms = PropositionalAtoms()
    pa_network = pham_pt_directDomEnc(qcn, instance, atoms)

    # encode PA theory
    for i in range(0, qcn.size):
        for j in range(i, qcn.size):
            for k in range(j, qcn.size):
                for s1 in ['-', '+']:  # pylint: disable=C0103
                    for s2 in ['-', '+']:  # pylint: disable=C0103
                        if i == j and s1 >= s2:
                            continue
                        if i != j and qcn.graph and (i, j) not in qcn.graph:
                            continue
                        for s3 in ['-', '+']:  # pylint: disable=C0103
                            if (i == k and s1 >= s3) or (j == k and s2 >= s3):
                                continue
                            if i != k and qcn.graph and (i, k) not in qcn.graph:
                                continue
                            if j != k and qcn.graph and (j, k) not in qcn.graph:
                                continue

                            for br1 in ['<', '=', '>']:
                                if br1+s1+s2 not in pa_network[i][j]:
                                    continue
                                b_ij = atoms.encode(i, j, br1+s1+s2)
                                for br2 in ['<', '=', '>']:
                                    if br2+s2+s3 not in pa_network[j][k]:
                                        continue
                                    support = list(pa_comp[br1+" "+br2])
                                    support.sort()
                                    b_jk = atoms.encode(j, k, br2+s2+s3)
                                    cl = [  # pylint: disable=C0103
                                        -1 * b_ij, -1 * b_jk ]
                                    for base_rel in support:
                                        if base_rel+s1+s3 in pa_network[i][k]:
                                            cl += [  # pylint: disable=C0103
                                                atoms.encode(i,
                                                    k, base_rel+s1+s3)]
                                    instance.add_clause(cl)

def pham_direct_pt_encode(qcn, instance):  # pylint: disable=R0914,R0912
    """Direct point-based encoding by Pham et al."""

    check_allen_signature(qcn.signature)

    pa_comp = point_algebra_comptable()
    from qcn2sat import PropositionalAtoms
    atoms = PropositionalAtoms()
    pa_network = pham_pt_directDomEnc(qcn, instance, atoms)

    # encode PA theory (direct)
    for i in range(0, qcn.size):
        for j in range(i, qcn.size):
            for k in range(j, qcn.size):
                for s1 in ['-', '+']:  # pylint: disable=C0103
                    for s2 in ['-', '+']:  # pylint: disable=C0103
                        if i == j and s1 >= s2:
                            continue
                        if i != j and qcn.graph and (i, j) not in qcn.graph:
                            continue
                        for s3 in ['-', '+']:  # pylint: disable=C0103
                            if (i == k and s1 >= s3) or (j == k and s2 >= s3):
                                continue
                            if i != k and qcn.graph and (i, k) not in qcn.graph:
                                continue
                            if j != k and qcn.graph and (j, k) not in qcn.graph:
                                continue

                            for br1 in ['<', '=', '>']:
                                if br1+s1+s2 not in pa_network[i][j]:
                                    continue
                                b_ij = atoms.encode(i, j, br1+s1+s2)
                                for br2 in ['<', '=', '>']:
                                    if br2+s2+s3 not in pa_network[j][k]:
                                        continue

                                    b_jk = atoms.encode(j, k, br2+s2+s3)

                                    rule_out = list(
                                        qcn.signature - pa_comp[br1+" "+br2])
                                    rule_out.sort()
                                    for base_rel in rule_out:
                                        if base_rel+s1+s3 in pa_network[i][k]:
                                            cl = [  # pylint: disable=C0103
                                                -1 * b_ij, -1 * b_jk
                                                ] + [ -1 * atoms.encode(
                                                    i, k, base_rel+s1+s3) ]
                                            instance.add_clause(cl)
