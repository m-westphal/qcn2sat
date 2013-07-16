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

    compate = [ predicate ]
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

def verify_is_fo_interpretation(syn_map):
    for relation in syn_map:
        relations = set(allen_signature)

        for clause in syn_map[relation]:
            relations &= evaluate_clause(clause)

        if relation != relations:
            print "Defining formula for %s broken" % relation
            print syn_map[relation]
            print "yields"
            print relations
            print

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

    print "Verify map is a FO interpretation"
    verify_is_fo_interpretation(syn_map)

#    write_map(syn_map)

#    stat_map(syn_map)
