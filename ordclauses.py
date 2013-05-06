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

import string

allen_signature = [ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di', 'm', 'mi', 'o', 'oi' ]
allen_relations = [ ]
ord_theory = None

class literal:
    def __init__(self, n, a, s1, r, b, s2):

        if r == '==':
            r = '='
        if n == '+':
            n = 'p'
        elif n == '-':
            n = 'n'

#        assert n != 'n' or r == "="
        assert r in ['<=', '=', '>=']
        assert n in ['p','n']

        self.n = n
        self.x = a
        self.s1 = s1
        self.y = b
        self.s2 = s2
        self.r = r

        self.canonical_form()

        self.hashvalue = self.n + self.x + self.s1 + self.r + self.y + self.s2
        self.hashvalue = self.hashvalue.__hash__()

    def __hash__(self):
        return self.hashvalue

    def __eq__(self, other):
        return (self.n,self.x,self.s1,self.r,self.y,self.s2) == (other.n,other.x,other.s1,other.r,other.y,other.s2)

    def __str__(self):
        s = None
        if self.n == 'n':
            s = '-'
        else:
            s = '+'
        s += '(' + self.x + self.s1 + ' '
        if len(self.r) == 1:
            s += '='
        s += self.r + ' ' + self.y + self.s2 + ')'
        return s

    def canonical_form(self):
        x = self.x
        y = self.y
        if x == 'y' and y == 'x':
            r = '='
            if self.r == '<=':
                r = '>='
            elif self.r == '>=':
                r = '<='
            (self.x, self.y) = ('x', 'y')
            (self.s1, self.s2) = (self.s2, self.s1)
            self.r = r
    def is_positive(self):
        if self.n == 'p':
            return True
        return False
    def get_atom(self):
        return (self.x,self.s1,self.r,self.y,self.s2)
    def get_negation(self):
        if self.n == 'p':
            return literal('n',self.x,self.s1,self.r,self.y,self.s2)
        return literal('p',self.x,self.s1,self.r,self.y,self.s2)

    def evaluate(self, br):
        p = self.n == 'p'

        if (self.x, self.s1) == (self.y, self.s2):
            return p

        s = string.join(self.get_atom())
        if s == 'x + = y +':
            return not (p ^ (br in [ '=', 'f', 'fi' ]))
        elif s == 'x - = y -':
            return not (p ^ (br in [ '=', 's', 'si' ]))
        elif s == 'x - = y +':
            return not (p ^ (br in [ 'mi' ]))
        elif s == 'x + = y -':
            return not (p ^ (br in [ 'm' ]))

        elif s == 'x - <= y -':
            return not (p ^ (br in [ '=', '<', 'm', 'o', 'fi', 'di', 's', 'si' ]))
        elif s == 'x - <= y +':
            return not (p ^ (br in [ '=', 'o', 'oi', '<', 'm', 'mi', 'f', 'fi', 'd', 'di', 's', 'si' ]))
        elif s == 'x + <= y -':
            return not (p ^ (br in [ '<', 'm' ] ) )
        elif s == 'x + <= y +':
            return not (p ^ (br in [ '=', '<', 'm', 'o', 'f', 'fi', 'd', 's', ]))

        elif s == 'x - >= y -':
            return not (p ^ (br in [ '=', '>', 'mi', 'oi', 'f', 'd', 's', 'si' ]))
        elif s == 'x - >= y +':
            return not (p ^ (br in [ 'mi', '>' ]))
        elif s == 'x + >= y -':
            return not (p ^ (br in [ '=', 'o', 'oi', 's', 'si', 'd', 'di', '>', 'm', 'mi', 'fi', 'f' ]))
        elif s == 'x + >= y +':
            return not (p ^ (br in [ '=', '>', 'f', 'fi', 'oi', 'mi', 'si', 'di' ]))
        elif s == 'y - >= y +':
            return not p
        elif s == 'x - = x +':
            return not p
        elif s == 'x + = x -':
            return not p

        elif s == 'x - <= x +':
            return p
        elif s == 'y - <= y +':
            return p
        elif s == 'y + <= y -':
            return not p
        elif s == 'x + <= x -':
            return not p
        elif s == 'y + <= y -':
            return not p
        elif s == 'x - = x +':
            return not p
        elif s == 'y - = y +':
            return not p
        elif s == 'y + = y -':
            return not p
        else:
            print "Undefined literal evaluation:", s, self.n == 'p'
        assert False

def evaluate_clause(clause, br):
    for l in clause:
        if l.evaluate(br):
            return True
#        else:
#            print "Unsat:", l
    return False

def evaluate_cnf(cnf, br):
    for cl in cnf:
        if not evaluate_clause(cl, br):
            return False
    return True

def base_relation_to_start_end_points(x,y,b):
    conj = set() # literals
    if b == '=':
        conj.add( literal('p',x,'-','=',y,'-') )
        conj.add( literal('p',x,'+','=',y,'+') )
        ###### complete ...
#        conj.add( literal('p',x,'-','<=',y,'-') )
#        conj.add( literal('p',x,'-','>=',y,'-') )
#        conj.add( literal('p',x,'+','<=',y, '+') )
#        conj.add( literal('p',x,'+','>=',y, '+') )
#        conj.add( literal('p',x,'-','<=',y,'+') )
#        conj.add( literal('p',x,'+','>=',y,'-') )

#        conj.add( literal('n',x,'-','=',y,'+') )
#        conj.add( literal('n',x,'+','=',y,'-') )
    elif b == '<':
        conj.add( literal('p',x,'+','<=',y,'-') )
        conj.add( literal('n',x,'+','=',y,'-') )
        ###### complete ...
#        conj.add( literal('p',x,'+','<=',y,'+') )
#        conj.add( literal('n',x,'+','=',y,'+') )
#        conj.add( literal('p',x,'-','<=',y,'-') )
#        conj.add( literal('n',x,'-','=',y,'-') )
#        conj.add( literal('p',x,'-','<=',y,'+') )
#        conj.add( literal('n',x,'-','=',y,'+') )
    elif b == '>':
        return base_relation_to_start_end_points(y,x,'<')
    elif b == 'm':
        conj.add( literal('p',x,'+','=',y,'-') )
#        conj.add( literal('p',x,'+','<=',y,'-') )
#        conj.add( literal('p',x,'+','>=',y,'-') )

#        conj.add( literal('p',x,'+','<=',y,'+') )
#        conj.add( literal('p',x,'-','<=',y,'-') )
#        conj.add( literal('p',x,'-','<=',y,'+') )
#        conj.add( literal('n',x,'+','=',y,'+') )
#        conj.add( literal('n',x,'-','=',y,'-') )
#        conj.add( literal('n',x,'-','=',y,'+') )
    elif b == 'mi':
        return base_relation_to_start_end_points(y,x,'m')
    elif b == 'd':
        conj.add( literal('p',y,'-','<=',x,'-') )
        conj.add( literal('n',y,'-','=',x,'-',) )
        conj.add( literal('p',x,'+','<=',y,'+') )
        conj.add( literal('n',x,'+','=',y,'+') )
        ###### complete ...
#        conj.add( literal('p',y,'-','<=',x,'+') )
#        conj.add( literal('n',y,'-','=',x,'+') )
#        conj.add( literal('p',x,'-','<=',y,'+') )
#        conj.add( literal('n',x,'-','=',y,'+') )
    elif b == 'di':
        return base_relation_to_start_end_points(y,x,'d')
    elif b == 's':
        conj.add( literal('p',x,'-','=',y,'-') )
#        conj.add( literal('p',x,'-','>=',y,'-') )
#        conj.add( literal('p',x,'-','<=',y,'-') )

        conj.add( literal('p',x,'+','<=',y,'+') )
        conj.add( literal('n',x,'+','=',y,'+') )

#        conj.add( literal('p',x,'-','<=',y,'+') )
#        conj.add( literal('p',x,'+','>=',y,'-') )
#        conj.add( literal('n',x,'+','=',y,'-') )
#        conj.add( literal('n',x,'-','=',y,'+') )
    elif b == 'si':
        return base_relation_to_start_end_points(y,x,'s')
    elif b == 'f':
#        conj.add( literal('p',x, '-','<=',y, '+') )
        conj.add( literal('p',x, '+','=', y, '+') )
#        conj.add( literal('p',x, '+','>=', y, '+') )
#        conj.add( literal('p',x, '+','<=', y, '+') )

        conj.add( literal('p',x, '-','>=',y, '-') )
        conj.add( literal('n',x, '-','=',y, '-') )

#        conj.add( literal('p',x, '+','>=', y, '-') )

#        conj.add( literal('n',x, '-','=', y, '+') )
    elif b == 'fi':
        return base_relation_to_start_end_points(y,x,'f')
    elif b == 'o':
        conj.add( literal('p',y,'-','<=',x,'+') )
        conj.add( literal('n',y,'-','=',x,'+') )
        conj.add( literal('p',x,'+','<=',y,'+') )
        conj.add( literal('n',x,'+','=', y,'+') )

        conj.add( literal('p',x,'-','<=',y,'-') )
        conj.add( literal('n',x,'-','=',y,'-') )

#        conj.add( literal('p',x,'-','<=',y,'+') )
#        conj.add( literal('n',x,'-','=',y,'+') )
#        conj.add( literal('n',x,'+','=',y,'-') )
    elif b == 'oi':
        return base_relation_to_start_end_points(y,x,'o')
    else: # unknown base relation
        assert False

    assert conj

    return conj

def __print_nf(formula):
    print "{",
    for x in formula:
        print "{",
        for a in x:
            print a,
        print "}",
    print "}"

def __is_horn(cnf):
    for c in cnf:
        if len([l for l in c if l.is_positive()] ) > 1:
            return False
    return True

def __smart_pool(f, l, debug=False):
    from multiprocessing import Pool, cpu_count

    if cpu_count() > 1 and not debug:
        pool = Pool()
        return pool.map(f, l)
    else:
        return map(f,l)

def dnf_to_cnf(dnf):
    import itertools

#    print "#d Generate CNF"

    cnf = set()

    for element in itertools.product(*dnf):
        cnf.add( frozenset(element) )

#    print "#d Finished CNF"
    return cnf

def simple_subsumption_testing(cnf, th): # QUITE SLOW TODO
    todo = [ cl for cl in cnf ]
    todo.sort(key=lambda x: len(x))

#    print "#d subsumption testing"
    fixpoint = False
    while not fixpoint:
        fixpoint = True
        for t in todo:
            for t2 in todo:
                if t == t2:
                    continue
                if t <= t2:
                    todo.remove(t2)
                    fixpoint = False
                    break
            if not fixpoint:
                break
            for c in th:
                if c <= t:
                    todo.remove(t)
                    fixpoint = False
                    break
            if not fixpoint:
                break

#    print "#d subsumption testing done"

    return set(todo)

def ordtheory():
    print "#d generate ordtheory"

    cnf = set()

    cnf.add( frozenset([literal('p', 'x', '-', '<=', 'x', '+')]) )
    cnf.add( frozenset([literal('n', 'x', '-', '=', 'x', '+')]) )
    cnf.add( frozenset([literal('p', 'y', '-', '<=', 'y', '+')]) )
    cnf.add( frozenset([literal('n', 'y', '-', '=', 'y', '+')]) )

    import itertools

    tup = ( ['x','y'], ['-', '+'])
    for p1 in itertools.product(*tup):
        cnf.add( frozenset([ literal('p', p1[0],p1[1], '<=', p1[0], p1[1]) ]) )
        for p2 in itertools.product(*tup):
            cnf.add( frozenset([ literal('n', p1[0],p1[1], '<=', p2[0], p2[1]), literal('n', p2[0], p2[1], '<=', p1[0], p1[1]), literal('p', p1[0], p1[1], '=', p2[0], p2[1])]))
            cnf.add( frozenset([ literal('n', p1[0],p1[1], '=', p2[0], p2[1]), literal('p', p1[0], p1[1], '<=', p2[0], p2[1])]))
            cnf.add( frozenset([ literal('n', p1[0],p1[1], '=', p2[0], p2[1]), literal('p', p1[0], p1[1], '>=', p2[0], p2[1])]))
            for p3 in itertools.product(*tup):
                cnf.add( frozenset([ literal('n', p1[0],p1[1], '<=', p2[0], p2[1]), literal('n', p2[0], p2[1], '<=', p3[0], p3[1]), literal('p', p1[0], p1[1], '<=', p3[0], p3[1])]))

    print "#d generated ordtheory"
    return frozenset(cnf)

def models(cnf, th):
    fcnf = frozenset(set(cnf)|set(th))

    res = set()
    for br in allen_signature:
        if evaluate_cnf(fcnf, br):
            res.add(br)

    return res

def redundant_clause(rel, cnf, th, cl):
    tmp = cnf.copy()
    tmp.remove(cl)

    if rel == models(tmp, th):
#        print "\t... kill clause",
#        __print_nf([cl])
        return tmp
#    else:
#        print "Removing clause",
#        __print_nf([cl])
#        print "\twould ALLOW", models(tmp, th) - rel

    return None

def redundant_literal(rel, cnf, th, cl):
    assert len(cl) > 1

    for sl in cl:
        tmp_cnf = cnf.copy()
        tmp_cnf.remove(cl)
        tmp_cl = frozenset([ l for l in cl if l != sl ])
        tmp_cnf.add(tmp_cl)
        if rel == models(tmp_cnf, th):
#            print "\t... kill literal", sl
            return tmp_cnf
#        else:
#            print "Removing literal", l, "in",
#            __print_nf([cl])
#            print "\twould REMOVE", rel - models(tmp_cnf, th)
    return None

def minimize_cnf(rel, cnf, th):
#    print "#d minimize cnf", len(cnf)

#    print "\t", rel, models(cnf, th), models(cnf, set())
    assert models(cnf, set()) >= models(cnf, th)
    assert rel == models(cnf, th)

    # try to remove non-horn clauses
    for cl in cnf:
        if not __is_horn([cl]):
            ncnf = redundant_clause(rel, cnf, th, cl)
            if not ncnf is None:
                return minimize_cnf(rel, ncnf, th)
    # try to minimize non-horn clauses
    for cl in cnf:
        if not __is_horn([cl]) and len(cl) > 1:
            ncnf = redundant_literal(rel, cnf, th, cl)
            if not ncnf is None:
                return minimize_cnf(rel, ncnf, th)
    # any other minimization ...
#    __print_nf(cnf)
#    print "Trying any clause"
    for cl in cnf:
        if len(cl) > 1:
            ncnf = redundant_literal(rel, cnf, th, cl)
            if not ncnf is None:
                return minimize_cnf(rel, ncnf, th)
    for cl in cnf:
        ncnf = redundant_clause(rel, cnf, th, cl)
        if not ncnf is None:
            return minimize_cnf(rel, ncnf, th)

#    print "#d minimized cnf", len(cnf)
    return cnf

def encode_test(relation_s):
#        cnf = nebel_buerckert_ordhorn(0,1, relation_s, boolvars)
#        __print_nf(cnf)

        dnf = set()
        for br in relation_s:
            dnf.add( frozenset(base_relation_to_start_end_points('x', 'y', br)) )

        cnf = dnf_to_cnf(dnf) 
        print "#d DNF->CNF with", len(cnf), "clauses"
        cnf = simple_subsumption_testing(cnf, ord_theory)
        cnf = minimize_cnf(relation_s, cnf, ord_theory)

        print "Relation", list(relation_s), "encoded as", len(cnf), "clauses",
        __print_nf(cnf)
        for br in allen_signature:
#            print "\t... test '", br, "' |= ^CNF^ ?",
            res = evaluate_cnf(frozenset( set(cnf)|set(ord_theory)), br)
#            print res
            if br in relation_s:
                assert res
            else:
                assert not res

        ### assert ORD-horn set
        if not ((__is_horn(cnf) and relation_s in ordhorn) or (not __is_horn(cnf) and not relation_s in ordhorn)):
            print "The relation", list(relation_s),
            if __is_horn(cnf):
                print "is erroneously represented as a horn clause!"
            else:
                print "is erroneously represented as a NON-horn clause!"
            for c in cnf:
                if len([t for t in c if t.is_positive()]) > 1:
                    __print_nf([c])
            print
            assert False
#        print "#d is ordhorn:", __is_horn(cnf), "Is in known ordhorn relations:", relation_s in ordhorn
#        if not __is_horn(cnf):
        assert (__is_horn(cnf) and relation_s in ordhorn) or (not __is_horn(cnf) and not relation_s in ordhorn)
        return cnf

if __name__ == '__main__':
    print "[Nebel/Bürckert] Generate map \pi for all relations"

    ord_theory = ordtheory()

    # read ord-horn relations for verification purposes
    ordhorn = set()

    flines = open('allen/hornalg', 'r')
    for line in flines:
        t = line[2:-3].split(' ')
        if t == ['']: # empty relation
            continue

        ordhorn.add( frozenset(t) )
    flines.close()

    ordhorn = frozenset(ordhorn)

    print "Generate list of relations"

    signature = allen_signature
    prod = [ ]
    for i in xrange(0,13):
        prod.append([True, False])

    import itertools
    relations = [ ]
    for bm in itertools.product(*prod):
        relation = set()
        for i in xrange(0,13):
            if bm[i]:
                relation.add(signature[i])

#        if relation and len(relation) > 9: # DEBUG
        if relation:
            relations.append(frozenset(relation))
    relations.sort(key=lambda x: len(x))
    allen_relations = relations

    print "Compute CNFs for all relations"
    cnf_definitions = [ ]
    result = __smart_pool(encode_test, relations, debug=False)

    import string
    print "Done computing"
    print
    for relation_s, res in zip(relations, result):
        print "x ( "+string.join(list(relation_s))+" ) y ::",
        __print_nf(res)
