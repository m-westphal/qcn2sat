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

RCC8_SIGNATURE = [ 'EQ', 'DC', 'EC', 'PO', 'TPP', 'NTPP', 'TPPI', 'NTPPI' ]

# description of base relations in terms of {P, NTP, DC, DR}
# See ("Logical Representations for Automated Reasoning about Spatial
# Relationships" Bennett) p. 90
FULL_DESCRIPTION = {
    'EQ': [ '+(x P y)', '+(y P x)' ],
    'DC': [ '-(x NDC y)'],
    'EC': [ '-(x O y)', '+(x NDC y)' ],
    'PO': [ '+(x O y)', '-(x P y)', '-(y P x)' ],
    'TPP': [ '+(x P y)', '-(y P x)', '-(x NTP y)' ],
    'TPPI': [ '+(y P x)', '-(x P y)', '-(y NTP x)' ],
    'NTPP': [ '+(x NTP y)' ],
    'NTPPI': [ '+(y NTP x)' ]
}

def form_literal(string):
    from syntactic_map import Predicate

    positive = True
    if string[0] == '-':
        positive = False
    else:
        assert string[0] == '+'
    return (positive, Predicate(string[2:-1]))

def _assert_is_horn(relation, cnf):
    try:
        lines = open('hornalg', 'r')
        found = False
        for l in lines:
            stuff = frozenset(l.split(' '))
            if set(relation) <= stuff and len(relation)+2 == len(stuff):
                found = True
                break
        lines.close()
        if not found:
            print "[ERROR] ... is erroneously horn"

            print relation
            print_cnf(cnf)
            return False

    except IOError, e:
        print "File 'hornalg': IO Error"

    return True

def _assert_is_not_horn(relation, cnf):
    try:
        lines = open('hornalg', 'r')
        for l in lines:
            stuff = frozenset(l.split(' '))
            if set(relation) <= stuff and len(relation)+2 == len(stuff):
                print "[ERROR] ... is not horn"

                print relation
                print_cnf(cnf)
                lines.close()
                return False

        lines.close()
    except IOError, e:
        print "File 'hornalg': IO Error"
    return True

def build_syn_int(output_map=False):
    from itertools import combinations


    relations = []
    for i in xrange(0,8):
        for relation in combinations(RCC8_SIGNATURE,i+1):
            relations.append(relation)

    print "Work on %d relations" % (len(relations))

    syn_map = dict()
    horn_relations = 0
    missed_horn = 0
    erroneously_horn = 0
    for relation in relations:
        dnf = set()
        for base_relation in relation:
            conjunction = [ ]
            for element in FULL_DESCRIPTION[base_relation]:
                conjunction.append( form_literal(element) )

            dnf.add(frozenset(conjunction))
        cnf = dnf_to_cnf(dnf)
        cnf = simplify_cnf(cnf)
        if frozenset(relation) != get_base_relations_satisfying_cnf(cnf):
            print "Failed to get simplified CNF for", relation
            print_cnf(cnf)
        assert frozenset(relation) == get_base_relations_satisfying_cnf(cnf)

        syn_map[relation] = cnf
#        print len(cnf)
#        print is_horn(cnf)
        if is_horn(cnf):
            if not _assert_is_horn(relation, cnf):
                erroneously_horn += 1
#            print "Is horn: ", relation
#            print cnf
            horn_relations += 1
        else:
            if not _assert_is_not_horn(relation, cnf):
                missed_horn += 1
#            if len(cnf) < 3:
#                print relation
#                print_cnf(cnf)
#                print

    print "Horn statistics (there must be 147+1 such relations)"
    print "\t%d generated horn" % horn_relations
    print "\t%d erroneously horn (generated horn, but must not be)" % erroneously_horn
    print "\t%d missed horn relations" % missed_horn

    if output_map:
        from syntactic_map import print_map
        print_map(syn_map)

def print_cnf(cnf):
    print "CNF %d clause(s)" % len(cnf)
    for clause in cnf:
        print "(",
        for idx, literal in enumerate(clause):
            if not literal[0]:
                print "not (",
            print literal[1].string,
            if not literal[0]:
                print ")",

            if idx+1 < len(clause):
                print "or",
        print ") and",
    print "( T )"
    for clause in cnf:
        print "Origin(?)",
        print get_base_relations_satisfying_cl(clause)

    print get_base_relations_satisfying_cnf(cnf)


def dnf_to_cnf(dnf):
    import itertools
    cnf = set()
    for element in itertools.product(*dnf):
        cnf.add( frozenset(element) )
    return cnf

def simplify_cnf(cnf):
    from copy import deepcopy

    fixpoint = False
    while not fixpoint:
        fixpoint = True

        copy = deepcopy(cnf)
        for clause in copy:
            for clause2 in copy:
                if clause != clause2 and clause <= clause2:
                    fixpoint = False
                    cnf.discard(clause2)

        if fixpoint:
            for clause in copy:
                if clause_tautology(clause):
                    fixpoint = False
                    cnf.discard(clause)
        if fixpoint:
            relation = get_base_relations_satisfying_cnf(cnf)
            for clause in copy:
                for literal in clause:
                    clause_copy = set(deepcopy(clause))
                    clause_copy.remove(literal)

                    if relation == get_base_relations_satisfying_cnf([x for x in copy if x != clause]+[clause_copy]):
                        fixpoint = False
                        cnf.remove(clause)
                        if clause_copy:
                            cnf.add(frozenset(clause_copy))
                        break
                if not fixpoint:
                    break

    return cnf 

def clause_tautology(clause):
    for literal in clause:
        for literal2 in clause:
            if literal[0] != literal2[0] and literal[1] == literal2[1]:
                return True

    return False

def get_base_relations_satisfying_cnf(cnf):
    intersection = set(RCC8_SIGNATURE)
    for clause in cnf:
        intersection &= get_base_relations_satisfying_cl(clause)

    return intersection

def rules(facts):
    from syntactic_map import Predicate

    my_rules = [
        # *symmetry
        ([(True, Predicate('x NTP y'))], (False, Predicate('y NTP x'))),
        ([(True, Predicate('y NTP x'))], (False, Predicate('x NTP y'))),
        ([(True, Predicate('x NDC y'))], (True, Predicate('y NDC x'))),
        ([(True, Predicate('y NDC x'))], (True, Predicate('x NDC y'))),
        ([(False, Predicate('x NDC y'))], (False, Predicate('y NDC x'))),
        ([(False, Predicate('y NDC x'))], (False, Predicate('x NDC y'))),
        ([(True, Predicate('x O y'))], (True, Predicate('y O x'))),
        ([(True, Predicate('y O x'))], (True, Predicate('x O y'))),
        ([(False, Predicate('x O y'))], (False, Predicate('y O x'))),
        ([(False, Predicate('y O x'))], (False, Predicate('x O y'))),
        # DC
        ([(False, Predicate('x NDC y'))], (False, Predicate('x P y'))),
        ([(False, Predicate('x NDC y'))], (False, Predicate('y P x'))),
        ([(False, Predicate('x NDC y'))], (False, Predicate('x NTP y'))),
        ([(False, Predicate('y NDC x'))], (False, Predicate('x NTP y'))),
        ([(False, Predicate('x NDC y'))], (False, Predicate('y NTP x'))),
        ([(False, Predicate('y NDC x'))], (False, Predicate('y NTP x'))),
        ([(False, Predicate('x NDC y'))], (False, Predicate('x O y'))),
        # NTP
        ([(True, Predicate('x NTP y'))], (True, Predicate('x P y'))),
        ([(True, Predicate('y NTP x'))], (True, Predicate('y P x'))),
        ([(True, Predicate('x NTP y'))], (False, Predicate('y P x'))),
        ([(True, Predicate('y NTP x'))], (False, Predicate('x P y'))),
        ([(True, Predicate('x NTP y'))], (True, Predicate('x NDC y'))),
        ([(True, Predicate('y NTP x'))], (True, Predicate('x NDC y'))),
        # P
        ([(True, Predicate('x P y'))], (True, Predicate('x NDC y'))),
        ([(True, Predicate('y P x'))], (True, Predicate('x NDC y'))),
        # ODD?!?!?!
        ([(False, Predicate('x O y')), (True, Predicate('x NDC y'))], (False, Predicate('x P y'))),
        ([(False, Predicate('x O y')), (True, Predicate('x NDC y'))], (False, Predicate('y P x'))),
        ([(True, Predicate('x O y'))], (True, Predicate('x NDC y'))),

        ([(True, Predicate('x EC y'))], (False, Predicate('x O y'))),
        ([(True, Predicate('x P y'))], (True, Predicate('x O y'))),
        ([(True, Predicate('y P x'))], (True, Predicate('x O y'))),
        ([(False, Predicate('x O y'))], (False, Predicate('x NTP y'))),
        ([(True, Predicate('x P y'))], (False, Predicate('y NTP x'))),
        ([(True, Predicate('y P x'))], (False, Predicate('x NTP y'))),
        ([(False, Predicate('x P y'))], (False, Predicate('x NTP y'))),
        ([(False, Predicate('y P x'))], (False, Predicate('y NTP x'))),
    ]
    # print len(my_rules)/2
    
    # TODO write proper Datalog engine :/
    # TODO add facts, derive conflicts

    # TODO needs set semantics (list grows infinite x DC y => y DC x => x DC y ...

    for body, head in my_rules:
        sat = True
        for req in body:
            if not req in facts:
                sat = False
                break
        if sat:
            facts.add(head)
        
    return facts

def get_true_facts(facts):
    nr_facts = 0
    while len(facts) != nr_facts:
        nr_facts = len(facts)

        rules(facts)

    for x in facts:
        assert (x[0]^True, x[1]) not in facts

    return facts

def get_base_relations_satisfying_cl(clause):
    res = [ ]

    for br in FULL_DESCRIPTION:
        conjunction = FULL_DESCRIPTION[br]

        facts = set()
        for string in conjunction:
            facts.add(form_literal(string))

        facts = get_true_facts(facts)
        sat = False
        for true_f in facts:
            if true_f in clause:
                sat = True
                break
        if sat:
            res.append(br)

    return frozenset(res)

def is_horn(cnf):
    for clause in cnf:
        pos_atoms = 0
        for literal in clause:
            if literal[0]:
                pos_atoms += 1
        if pos_atoms > 1:
            return False

    return True

def self_test():
    print "Self test"

    for base_relation in RCC8_SIGNATURE:
        cnf = set()
        for conj in FULL_DESCRIPTION[base_relation]:
            cnf.add( frozenset( [ form_literal(conj) ] ) )

        base_relation_sat = get_base_relations_satisfying_cnf(cnf)
        if frozenset([base_relation]) != base_relation_sat:
            print base_relation, "!=", base_relation_sat
            print_cnf(cnf)

        assert frozenset([base_relation]) == base_relation_sat

    print "Self test OK"

#def unit_resolution(cnf):
#    import copy
#
#    fixpoint = False
#    while not fixpoint:
#        units = [ x for x in cnf if len(x) == 1 ]
#        for x in units:
#            for y in units:
#                if x == y:
#                    continue
#                if x.relation

#    return cnf
        

def is_rcc8_interpretation(syntactic_map):
    """Check input signature of syntactic map."""
    symbols = set()
    for relation in syntactic_map:
        for base in relation:
            symbols.add(base)

    if symbols != frozenset(RCC8_SIGNATURE):
        raise SystemExit('Given signature does not match RCC8 signature')

def evaluate_predicate(atom):
    """Return RCC8 base relations satisfied by given atom."""

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

def verify_is_fo_interpretation(syntactic_map):
    """Test all defining formulas in syntactic map."""
    is_valid = True
    for relation in syntactic_map:
        relations = get_base_relations_satisfying_cnf(syntactic_map[relation])

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
                if relation <= get_base_relations_satisfying_cl(mod_clause):
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

            if relation == get_base_relations_satisfying_cnf(mod_formula):
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
    # TMP CODE

    self_test()
#    build_syn_int(True)

#    from qcn2sat import read_comp_table
#    COMP, SIG = read_comp_table(MAP_FILE)

#    assert SIG == frozenset(RCC8_SIGNATURE)

    from syntactic_map import read_map  # pylint: disable=F0401

    SYNTACTIC_MAP = read_map(MAP_FILE)
    print "DONE"

    is_rcc8_interpretation(SYNTACTIC_MAP)

    print
    print "Verify map is a FO interpretation"
    if not verify_is_fo_interpretation(SYNTACTIC_MAP):
        raise SystemExit("Aborting script. Fix map first to run further tests.")
    print "... is valid"

    print
    print "Verify minimality of defining formulas"
    if verify_minimality(SYNTACTIC_MAP):
        print "... act as prime implicates."
