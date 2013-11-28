#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""RCC8 specific functions."""

# ex: set tabstop=4 expandtab softtabstop=4:

# qcn2sat.py: convert qualitative constraint networks to propositional CNF
# Copyright (C) 2009-2013  Matthias Westphal
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

def check_rcc8_signature(signature):
    """Check if signature is Allen signature."""

    rcc8_signature = [ 'EQ', 'DC', 'EC', 'PO', 'TPP', 'NTPP', 'TPPI', 'NTPPI' ]

    if signature != frozenset(rcc8_signature):
        raise SystemExit('Given signature does not match RCC8 signature')

def instantiate(l, x, y, atoms): # pylint: disable=C0103
    """encode instantiated literal l on x,y"""

    assert l[1].relation in [ 'NDC', 'O', 'NTP', 'P' ]

    mod = 1
    if not l[0]:  # negated predicate
        mod = -1

    # symmetry
    if l[1].relation in [ 'O', 'NDC' ]:
        if y < x:
            rel_string = l[1].swap_variables_string()
            rel_string = rel_string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
            return mod * atoms.encode(y, x, rel_string)
        else:
            rel_string = l[1].string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
            return mod * atoms.encode(x, y, rel_string)

    # asymmetry
    if l[1].relation == 'NTP':
        if y < x:
            rel_string = l[1].swap_variables_string()
            rel_string = rel_string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
            return -1 * mod * atoms.encode(y, x, rel_string)
        else:
            rel_string = l[1].string.replace('x', str(x))
            rel_string = rel_string.replace('y', str(y))
            return mod * atoms.encode(x, y, rel_string)

    # relation is 'P'
    rel_string = l[1].string.replace('x', str(x))
    rel_string = rel_string.replace('y', str(y))

    if x < y:
        return mod * atoms.encode(x, y, rel_string)
    # PropositionalAtoms::encode() assumes a <= b
    # The string is NOT rewritten ... It just gets filed under (y,x)
    return mod * atoms.encode(y, x, rel_string)


def rcc8_rcc7_encode_input(qcn, instance, atoms):
    """Encode instance according to RCC8->RCC7 map (but not the RCC7-theory)."""

    import os.path
    from syntactic_map import read_map
    syntactic_interpretation = \
        read_map(os.path.join('data', 'rcc8_rcc7.map'))

    for i, j in qcn.iterate_strict_triangle():
        relation = qcn.get(i, j)

        for clause in syntactic_interpretation[frozenset(relation)]:
            new_clause = [ ]
            for l in clause:  # pylint: disable=C0103
                new_clause.append( instantiate(l, i, j, atoms) )

            instance.add_clause( new_clause )


def rcc8_rcc7_encode_theory(qcn, instance, atoms):
    print 'TODO REST OF ENCODING'

    # encode RCC7 theory
    from syntactic_map import Predicate

    # "intersection" rules

    # RCC8 JEPD
    # RCC7
    # MUTEX:
    #   NTP DC
    #   O   DC
    #   P   DC


    # Propositional semantics (not Datalog):
    # A -> B equiv \not B -> \not A
    rules_2 = [ ([ (False, Predicate("x NDC y") ], (False, Predicate("x P y")),
                ([ (False, Predicate("x NDC y") ], (False, Predicate("x NTP y")),
                ([ (False, Predicate("x NDC y") ], (False, Predicate("y NTP x")),
                ([ (False, Predicate("x NDC y") ], (False, Predicate("x O y")),
            ]
        # NTP
#        ([(True, Predicate('x NTP y'))], (True, Predicate('x P y'))),
#        ([(True, Predicate('y NTP x'))], (True, Predicate('y P x'))),
#        ([(True, Predicate('x NTP y'))], (False, Predicate('y P x'))),
#        ([(True, Predicate('y NTP x'))], (False, Predicate('x P y'))),
#        ([(True, Predicate('x NTP y'))], (True, Predicate('x NDC y'))),
#        ([(True, Predicate('y NTP x'))], (True, Predicate('x NDC y'))),
        # ODD?!?!?!
#        ([(False, Predicate('x O y')), (True, Predicate('x NDC y'))], (False, Predicate('x P y'))),
#        ([(False, Predicate('x O y')), (True, Predicate('x NDC y'))], (False, Predicate('y P x'))),
#        ([(True, Predicate('x O y'))], (True, Predicate('x NDC y'))),

#        ([(True, Predicate('x EC y'))], (False, Predicate('x O y'))),
#        ([(True, Predicate('x P y'))], (True, Predicate('x O y'))),
#        ([(True, Predicate('y P x'))], (True, Predicate('x O y'))),
#        ([(False, Predicate('x O y'))], (False, Predicate('x NTP y'))),
#        ([(True, Predicate('x P y'))], (False, Predicate('y NTP x'))),
#        ([(True, Predicate('y P x'))], (False, Predicate('x NTP y'))),
#        ([(False, Predicate('x P y'))], (False, Predicate('x NTP y'))),
#        ([(False, Predicate('y P x'))], (False, Predicate('y NTP x'))),


    # TODO 1-consistency
    for i in xrange(0, qcn.self.size):
        # P, (O implied), NDC, \not NTP
        pass

    for i, j in qcn.iterate_strict_triangle():
        assert i < j
        pass
        # CAREFUL; SOMETIMES NEEDS (j,i) as well!


    # TODO COPY THE AXIOMS FROM PAPER
    rules_3 = [ ([ (True, Predicate("x P y"), (True, Predicate("x P y") ], (True, Predicate("x PO y")), # BS EXAMPLE RULE
            ]

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
def rcc8_rcc7_encode(qcn, instance):
    """Encode instance according to RCC8->RCC7 map."""

    check_rcc8_signature(qcn.signature)

    from qcn2sat import PropositionalAtoms
    atoms = PropositionalAtoms()

    # encode input
    rcc8_rcc7_encode_input(qcn, instance, atoms)

    rcc8_rcc7_encode_theory(qcn, instance, atoms)
