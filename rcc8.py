#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""RCC8 specific functions."""

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
def check_rcc8_signature(signature):
    """Check if signature is RCC8 signature."""

    rcc8_signature = [ 'EQ', 'DC', 'EC', 'PO', 'TPP', 'NTPP', 'TPPI', 'NTPPI' ]

    if signature != frozenset(rcc8_signature):
        raise SystemExit('Given signature does not match RCC8 signature')

def instantiate(l, x, y, atoms): # pylint: disable=C0103
    """encode instantiated literal l on x,y"""

    assert l[1].relation in [ 'C', 'O', 'NTP', 'P' ]

    mod = 1
    if not l[0]:  # negated predicate
        mod = -1

    # symmetry
    if l[1].relation in [ 'O', 'C' ]:
        if y < x:
            rel_string = l[1].swap_variables_string()
            rel_string = rel_string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
            return mod * atoms.encode(y, x, rel_string)
        else:
            rel_string = l[1].string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
            return mod * atoms.encode(x, y, rel_string)

    # relation is 'P' or 'NTP'
    rel_string = l[1].string.replace('x', str(x))
    rel_string = rel_string.replace('y', str(y))

    if x < y:
        return mod * atoms.encode(x, y, rel_string)
    # PropositionalAtoms::encode() assumes a <= b
    # The string is NOT rewritten ... It just gets filed under (y,x)
    return mod * atoms.encode(y, x, rel_string)

def instantiate_up_to_z(l, x, y, z, atoms): # pylint: disable=C0103
    """Wrapper for instantiate supporting 3 vars"""
    from syntactic_map import Predicate

    if 'z' != l[1].var1 and 'z' != l[1].var2:
        return instantiate(l, x, y, atoms)

    if 'x' != l[1].var1 and 'x' != l[1].var2:
        name = l[1].string
        name = name.replace('y', 'x')
        name = name.replace('z', 'y')
        return instantiate((l[0], Predicate(name)), y, z, atoms)
    if 'y' != l[1].var1 and 'y' != l[1].var2:
        name = l[1].string
        name = name.replace('z', 'y')
        return instantiate((l[0], Predicate(name)), x, z, atoms)
    assert False


def rcc8_rcc4_encode_input(qcn, instance, atoms):
    """Encode instance according to RCC8->RCC4 map (but not the RCC4-theory)."""

    import os.path
    from syntactic_map import read_map
    syntactic_interpretation = \
        read_map(os.path.join('data', 'rcc8_rcc4.map'))

    for i, j in qcn.iterate_strict_triangle():
        relation = qcn.get(i, j)

        for clause in syntactic_interpretation[frozenset(relation)]:
            new_clause = [ ]
            for l in clause:  # pylint: disable=C0103
                new_clause.append( instantiate(l, i, j, atoms) )

            instance.add_clause( new_clause )


def rcc8_rcc4_encode_theory(qcn, instance, atoms):
    """Ground the RCC8-RCC4 theory on qcn"""

    # encode RCC8 Horn theory using RCC4
    from syntactic_map import Predicate

    # 1-consistency asserted by SCRIPT

    clauses_2 = [ [ (True, Predicate("x C y")), (False, Predicate("x O y")) ],
                  [ (True, Predicate("x O y")), (False, Predicate("x P y")) ],
                  [ (True, Predicate("x P y")), (False, Predicate("x NTP y")) ],
                  [ (False, Predicate("y P x")), (False, Predicate("x NTP y")) ]
            ]

    for i, j in qcn.iterate_strict_triangle():
        assert i < j

        for rule_2 in clauses_2:
            clause = [ instantiate(pred, i, j, atoms) for pred in rule_2 ]
            instance.add_clause(clause)
            clause_sym = [ instantiate(pred, j, i, atoms) for pred in rule_2 ]
            if frozenset(clause) != frozenset(clause_sym):
                instance.add_clause(clause_sym)

    clauses_3 = [ [ (True, Predicate("x C y")),
        (False, Predicate("x C z")), (False, Predicate("z P y")) ],
        [ (True, Predicate("x NTP z")),
        (False, Predicate("x NTP y")), (False, Predicate("y P z")) ],
        [ (True, Predicate("x NTP z")),
        (False, Predicate("x P y")), (False, Predicate("y NTP z")) ],
        [ (True, Predicate("x O y")),
        (False, Predicate("z NTP y")), (False, Predicate("x C z")) ],
        [ (True, Predicate("x O y")),
        (False, Predicate("x O z")), (False, Predicate("z P y")) ],
        [ (True, Predicate("x P y")),
        (False, Predicate("x P z")), (False, Predicate("z P y")) ],
        ]

    for i in range(0, qcn.size):
        for j in range(0, qcn.size):
            if i == j or (qcn.graph and (i, j) not in qcn.graph):
                continue
            for k in range(0, qcn.size):
                if i == k or (qcn.graph and (i, k) not in qcn.graph):
                    continue
                if j == k or (qcn.graph and (j, k) not in qcn.graph):
                    continue

                for rule in clauses_3:
                    clause = [
                        instantiate_up_to_z(pred, i, j, k, atoms)
                        for pred in rule ]

                    instance.add_clause(clause)


def rcc8_rcc4_encode(qcn, instance):
    """Encode instance according to RCC8->RCC4 map."""

    check_rcc8_signature(qcn.signature)

    from qcn2sat import PropositionalAtoms
    atoms = PropositionalAtoms()

    # encode input
    rcc8_rcc4_encode_input(qcn, instance, atoms)

    rcc8_rcc4_encode_theory(qcn, instance, atoms)
