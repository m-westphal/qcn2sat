#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Internal test script to run some test on .map files. Mostly undocumented."""

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

ALLEN_SIGNATURE = [ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di', 'm',
    'mi', 'o', 'oi' ]

# description of intervals (x,y) in terms of start (?,-) and endpoints (?,+)
FULL_POINT_DESCRIPTION = {
    '=': ['=--', '<-+', '>+-', '=++'],
    '<': ['<--', '<-+', '<+-', '<++'],
    '>': ['>--', '>-+', '>+-', '>++'],
    'd': ['>--', '<-+', '>+-', '<++'],
    'di': ['<--', '<-+', '>+-', '>++'],
    'o': ['<--', '<-+', '>+-', '<++'],
    'oi': ['>--', '<-+', '>+-', '>++'],
    'm': ['<--', '<-+', '=+-', '<++'],
    'mi': ['>--', '=-+', '>+-', '>++'],
    's': ['=--', '<-+', '>+-', '<++'],
    'si': ['=--', '<-+', '>+-', '>++'],
    'f': ['>--', '<-+', '>+-', '=++'],
    'fi': ['<--', '<-+', '>+-', '=++']
}

def is_allen_interpretation(syntactic_map):
    """Check input signature of syntactic map."""
    symbols = set()
    for relation in syntactic_map:
        for base in relation:
            symbols.add(base)

    if symbols != frozenset(ALLEN_SIGNATURE):
        raise SystemExit('Given signature does not match Allen signature')

def evaluate_predicate(atom):
    """Return Allen base relations satisfied by given atom."""

    sig_1 = atom.var1[1]
    predicate = atom.relation
    sig_2 = atom.var2[1]

    if atom.var2[0] < atom.var1[0]:
        if predicate == '<=':
            predicate = '>='
        elif predicate == '>=':
            predicate = '<='
        elif predicate == '<':
            predicate = '>'
        elif predicate == '>':
            predicate = '<'
        (sig_2, sig_1) = (sig_1, sig_2)

    compare = [ predicate ]
    if predicate == "<=":
        compare = [ '<', '=' ]
    elif predicate == ">=":
        compare = [ '>', '=' ]

    relations = set()
    for base_relation in ALLEN_SIGNATURE:
        for prop in FULL_POINT_DESCRIPTION[base_relation]:
            if prop[1:] != sig_1+sig_2:
                continue
            for base in compare:
                assert base in [ '<', '=', '>' ]
                if base == prop[0]:
                    relations.add(base_relation)

    return relations

def evaluate_atom(literal):
    """Return Allen base relations satisfying given literal."""
    relations = evaluate_predicate(literal[1])
    if literal[0]:
        return relations
    return set(ALLEN_SIGNATURE) ^ relations

def evaluate_clause(clause):
    """Return Allen base relations satisfying given clause."""
    relations = set()
    for atom in clause:
        relations |= evaluate_atom(atom)
    
    return relations

def evaluate_cnf(cnf):
    """Return Allen base relations satisfying given CNF."""
    relations = set(ALLEN_SIGNATURE)
    for clause in cnf:
        relations &= evaluate_clause(clause)

    return relations

def verify_is_fo_interpretation(syntactic_map):
    """Test all defining formulas in syntactic map."""
    is_valid = True
    for relation in syntactic_map:
        relations = evaluate_cnf(syntactic_map[relation])

        if relation != relations:
            print "Defining formula for %s broken" % relation
            print syntactic_map[relation]
            print "yields"
            print relations
            print
            is_valid = False
    return is_valid

def verify_minimality(syntactic_map):
    """Test non-redundant list of prime implicates."""
    from copy import deepcopy

    for relation in syntactic_map:
        def_formula = syntactic_map[relation]

        for clause in syntactic_map[relation]:
            if len(clause) == 1:
                continue
            for atom in clause:
                mod_clause = set(clause)
                mod_clause.remove(atom)
                if relation <= evaluate_clause(mod_clause):
                    print "Defining formula for %s broken" % relation
                    print "Formula is"
                    print syntactic_map[relation]
                    print "Clause"
                    print clause
                    print "is however not a PRIME implicate."

                    return False

        mod_formula = None
        for clause in syntactic_map[relation]:
            mod_formula = deepcopy(def_formula)
            mod_formula.remove(clause)

            if relation == evaluate_cnf(mod_formula):
                print "Relation '%s' is not minimally defined:" % relation
                print
                print "Original defintion"
                print def_formula
                print
                print "Yet, removing"
                print clause
                print "does NOT invalidate formula."
                print "Thus, a useless clause."

                return False

    return True

if __name__ == '__main__':
    from sys import argv

    if len(argv) != 2:
        print "Script for verifying syntactic maps of Allen's Interval Calculus"
        print
        print "Usage: scrip <some.map>"

    MAP_FILE = argv[1]
    print "Read '%s'" % (MAP_FILE)

    import sys, os
    sys.path.insert(1, os.path.join(sys.path[0], '..'))
    from syntactic_map import read_map  # pylint: disable=F0401

    SYNTACTIC_MAP = read_map(MAP_FILE)
    print "DONE"

    is_allen_interpretation(SYNTACTIC_MAP)

    print
    print "Verify map is a FO interpretation"
    if not verify_is_fo_interpretation(SYNTACTIC_MAP):
        raise SystemExit("Aborting script. Fix map first to run further tests.")
    print "... is valid"

    print
    print "Verify minimality of defining formulas"
    if verify_minimality(SYNTACTIC_MAP):
        print "... act as prime implicates."
