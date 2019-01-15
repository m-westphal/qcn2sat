#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Functions for syntactic maps"""

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
from __future__ import print_function
class Predicate:  # pylint: disable=R0903
    """Relation with arguments."""
    def __init__(self, string, var1=None, rel=None, var2=None):
        if string is None:
            self.var1 = var1
            self.relation = rel
            self.var2 = var2
            self.string = "%s %s %s" % (var1, rel, var2)
        else:
            import re

            match = re.match(r'^([xyz+-]+) ([<=>A-Z]+) ([xyz+-]+)$', string)

            rel = match.group(2)

            self.var1 = match.group(1)
            self.relation = rel
            self.var2 = match.group(3)
            self.string = string

        self.hashvalue = self.var1 + self.var2 + self.relation
        self.hashvalue = self.hashvalue.__hash__()

    def swap_variables_string(self):
        """Swap arguments for relation, but not the relation itself."""
        return "%s %s %s" % (self.var2, self.relation, self.var1)

    def __eq__(self, other):
        return self.var1 == other.var1 and self.var2 == other.var2 and \
            self.relation == other.relation

    def __hash__(self):
        return self.hashvalue

def read_map(filename):
    """Read map from 'filename', return dict."""
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
                msg = "Relation symbol '%s' appears twice in map" % (relation)
                raise SystemExit(msg)
            assert not relation in syn_map

            defining_formula = match.group(2).strip()

            cnf = parse_cnf_string(defining_formula)

            syn_map[relation] = cnf
        else:
            msg = "Failed to parse syntactic map in '%s', line '%s'" % (
                filename, line)
            raise SystemExit(msg)

    content.close()

    return syn_map

def parse_cnf_string(string):
    """Parse string denoting a CNF (defining) formula."""
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

            positive = True
            if match.group(1) == '-':
                positive = False

            clause_set.add( (positive, Predicate(match.group(2))) )
        cnf.add( frozenset(clause_set) )

    return cnf

def print_map(syn_map):
    """Print a map to stdout in sorted order."""

    sorted_map = dict()
    for relation in syn_map.keys():
        elements = list(relation)

        elements.sort()
        name = ' '.join(elements)

        sorted_clauses = list()
        for clause in syn_map[relation]:
            sorted_clause = list(clause)
            sorted_clause.sort()
            sorted_clauses.append(sorted_clause)
        sorted_clauses.sort()

        sorted_map[name] = sorted_clauses
    
    names = list(sorted_map.keys())
    names.sort()
    for name in names:
        clauses_str = ""
        for clause in sorted_map[name]:
            clause_str = " {"
            for atom in clause:
                mod = '+'
                if not atom[0]:
                    mod = '-'
                clause_str += " %s(%s)" % (mod, atom[1].string)
            clause_str += " }"
            clauses_str += clause_str
         
        print("x ( %s ) y :: {%s }" % (name, clauses_str))

def is_horn_clause(clause):
    """Is clause a Horn-clause?"""

    pos = False
    for atom in clause:
        if atom[0]:
            if pos:
                return False
            pos = True
    return True

def is_horn_formula(formula):
    """Is formula a horn formula?"""

    for clause in formula:
        if not is_horn_clause(clause):
            return False
    return True

def is_primitive_formula(formula):
    """Is formula purely conjunctive?"""

    for clause in formula:
        if len(clause) > 1:
            return False
    return True

def stat_map(syn_map):
    """Print some statistics on given map."""

    print("Map statistics")
    print()
    print("Defines %d relations" % len(syn_map))


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
                if atom[0]:
                    positive_atoms += 1
                else:
                    negative_atoms += 1

    print("Total clauses in map:\t%10u" % clauses)
    print("Total atoms in map:\t%10u" % atoms)
    print("Positive atoms:\t\t%10u" % positive_atoms)
    print("Negative atoms:\t\t%10u" % negative_atoms)
    print("Unit clauses:\t\t%10u" % unit_clauses)
    print("Horn clauses:\t\t%10u" % horn_clauses)
    print()
    print("Primitive relations:\t%10u (%.3f)" % (
        primitive_relations, float(primitive_relations) / len(syn_map)))
    print("Horn relations:\t\t%10u (%.3f)" % (
        horn_relations, float(horn_relations) / len(syn_map)))

if __name__ == '__main__':
    print("Utility script for syntactic maps")
    print()
    print("Usage: scrip <some.map>")

    from sys import argv
    MAP_FILE = argv[1]
    print("Read '%s'" % (MAP_FILE))
    SYN_MAP = read_map(MAP_FILE)
    print("DONE")

    print("Sorted map")
    print_map(SYN_MAP)

    stat_map(SYN_MAP)
