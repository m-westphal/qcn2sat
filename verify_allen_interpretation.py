#! /usr/bin/env python
# -*- coding: UTF-8 -*-

# ex: set tabstop=4 expandtab softtabstop=4:

# qcsp2sat.py: convert qualitative CSPs to CNF formulae
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

#from ordclauses import literal
#from qcsp2sat import PropositionalAtoms

allen_signature = [ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di', 'm', 'mi', 'o', 'oi' ]

full_point_description = {
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

def is_allen_interpretation(syn_map):
    symbols = set()
    for relation in syn_map:
        for base in relation:
            symbols.add(base)

    if symbols != frozenset(allen_signature):
        raise SystemExit('Given signature does not match Allen signature')

def evaluate_pos_atom(atom):
    import re
    match = re.match(r'^x([+-]) (.*) y([+-])$', atom)

    sig_1 = match.group(1)
    predicate = match.group(2)
    sig_2 = match.group(3)

    compare = [ predicate ]
    if predicate == "<=":
        compare = [ '<', '=' ]
    elif predicate == "==":
        compare = [ '=' ]
    elif predicate == ">=":
        compare = [ '>', '=' ]

    relations = set()
    for br in allen_signature:
        for prop in full_point_description[br]:
            if prop[1:] != sig_1+sig_2:
                continue
            for base in compare:
                assert base in [ '<', '=', '>' ]
                if base == prop[0]:
                    relations.add(br)

    return relations

def evaluate_atom(atom):
    relations = evaluate_pos_atom(atom[1])
    if atom[0] == '+':
        return relations
    return set(allen_signature) ^ relations

def evaluate_clause(clause):
    relations = set()
    for atom in clause:
        relations |= evaluate_atom(atom)
    
    return relations

def evaluate_cnf(cnf):
    relations = set(allen_signature)
    for clause in cnf:
        relations &= evaluate_clause(clause)

    return relations

def verify_is_fo_interpretation(syn_map):
    is_valid = True
    for relation in syn_map:
        relations = evaluate_cnf(syn_map[relation])

        if relation != relations:
            print "Defining formula for %s broken" % relation
            print syn_map[relation]
            print "yields"
            print relations
            print
            is_valid = False
    return is_valid

def verify_minimality(syn_map):
    """Non-redundant list of prime implicates"""
    from copy import deepcopy

    for r in syn_map:
        def_formula = syn_map[r]

        for clause in syn_map[r]:
            if len(clause) == 1:
                continue
            for atom in clause:
                mod_clause = set(clause)
                mod_clause.remove(atom)
                if r <= evaluate_clause(mod_clause):
                    print "Defining formula for %s broken" % relation
                    print "Formula is"
                    print syn_map[r]
                    print "Clause"
                    print clause
                    print "is however not a PRIME implicate."

                    return False

        mod_formula = None
        for clause in syn_map[r]:
            mod_formula = deepcopy(def_formula)
            mod_formula.remove(clause)

            if r == evaluate_cnf(mod_formula):
                print "Relation '%s' is not minimally defined:" % r
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
    print "Script for verifying syntactic maps of Allen's Interval Calculus"
    print
    print "Usage: scrip <some.map>"

    from sys import argv
    map_file = argv[1]
    print "Read '%s'" % (map_file)
    from syntactic_map import read_map
    syn_map = read_map(map_file)
    print "DONE"

    is_allen_interpretation(syn_map)

    print
    print "Verify map is a FO interpretation"
    if not verify_is_fo_interpretation(syn_map):
        raise SystemExit("Aborting script. Fix map first to run further tests.")
    print "... is valid"

    print
    print "Verify minimality of defining formulas"
    if verify_minimality(syn_map):
        print "... act as prime implicates."
