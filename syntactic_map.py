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

import string

def read_map(filename):
    import re

    content = open(filename, 'r')

    # map style
    regexp = re.compile(r'^x \((.*)\) y :: {(.*)}$')

    syn_map = dict()
    for line in content:
        match = re.match(regexp, line)
        if match:
            org_string = match.group(1)
            relation = frozenset(org_string.strip().split(' '))
            if relation in syn_map:
                raise SystemExit("Relation symbol '%s' appears twice in map" % (relation))
            assert not relation in syn_map

            defining_formula = match.group(2).strip()

            cnf = parse_cnf_string(defining_formula)

            syn_map[relation] = cnf
        else:
            raise SystemExit("Failed to parse syntactic map in '%s', line '%s'" % (filename, line))

    content.close()

    return syn_map

def parse_cnf_string(string):
    import re

    clause_regexp = re.compile(r'^{([^}]+)}(.*)')

    string = string.strip()

    clauses = [ ]
    while string:
        clause = re.match(clause_regexp, string)
        clauses.append(clause.group(1).strip())
        string = clause.group(2).strip()

    atom_regexp = re.compile(r'^([+-])\(([^)]+)\)(.*)')

    cnf = set()
    for clause in clauses:
        clause_set = set()
        while clause:
            match = re.match(atom_regexp, clause)
            if not match:
                raise SystemExit("Failed to parse clause '%s'" % (clause))
            clause = match.group(3).strip()

            clause_set.add( (match.group(1), match.group(2)) )
        cnf.add( frozenset(clause_set) )

    return cnf

def write_map(syn_map):
    sorted_map = dict()
    for relation in syn_map.keys():
        elements = list(relation)

        elements.sort()
        from string import join
        name = join(elements)

        sorted_clauses = list()
        for clause in syn_map[relation]:
            sorted_clause = list(clause)
            sorted_clause.sort()
            sorted_clauses.append(sorted_clause)
        sorted_clauses.sort()

        sorted_map[name] = sorted_clauses
    
    names = sorted_map.keys()
    names.sort()
    for name in names:
        clauses_str = ""
        from string import join
        for clause in sorted_map[name]:
            clause_str = " {"
            for atom in clause:
                clause_str += " %s(%s)" % (atom)
            clause_str += " }"
            clauses_str += clause_str
         
        print "x ( %s ) y :: { %s }" % (name, clauses_str)

def is_horn_clause(clause):
    pos = False
    for atom in clause:
        if atom[0] == '+':
            if pos:
                return False
            pos = True
    return True

def is_horn_formula(formula):
    for clause in formula:
        if not is_horn_clause(clause):
            return False
    return True

def is_primitive_formula(formula):
    """Purely conjunctional formula"""
    for clause in formula:
        if len(clause) > 1:
            return False
    return True

def stat_map(syn_map):
    print "Map statistics"
    print
    print "Defines %d relations" % len(syn_map)


    clauses = 0
    atoms = 0
    positive_atoms = 0
    negative_atoms = 0
    unit_clauses = 0
    horn_clauses = 0
    primitive_relations = 0
    horn_relations = 0
    for relation in syn_map:
        defining_formula = syn_map[relation]
        clauses += len(defining_formula)


        if is_primitive_formula(defining_formula):
            primitive_relations += 1
        if is_horn_formula(defining_formula):
            horn_relations += 1

        for clause in defining_formula:
            if len(clause) == 1:
                unit_clauses += 1
            if is_horn_clause(clause):
                horn_clauses += 1
            atoms += len(clause)
            for atom in clause:
                if atom[0] == '+':
                    positive_atoms += 1
                elif atom[0] == '-':
                    negative_atoms += 1
                else:
                    assert False


    print "Total clauses in map:\t%10u" % clauses
    print "Total atoms in map:\t%10u" % atoms
    print "Positive atoms:\t\t%10u" % positive_atoms
    print "Negative atoms:\t\t%10u" % negative_atoms
    print "Unit clauses:\t\t%10u" % unit_clauses
    print "Horn clauses:\t\t%10u" % horn_clauses
    print
    print "Primitive relations:\t%10u (%.3f)" % (primitive_relations, float(primitive_relations) / len(syn_map))
    print "Horn relations:\t\t%10u (%.3f)" % (horn_relations, float(horn_relations) / len(syn_map))

if __name__ == '__main__':
    print "Utility script for syntactic maps"
    print
    print "Usage: scrip <some.map>"

    from sys import argv
    map_file = argv[1]
    print "Read '%s'" % (map_file)
    syn_map = read_map(map_file)
    print "DONE"

    print "Sorted map"
    write_map(syn_map)

    stat_map(syn_map)
