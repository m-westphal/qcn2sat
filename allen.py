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

def encodeDict(i, j, baserel, d):   # assign a boolean variable id to baserel in R_ij
    try:
        return d[i][j][baserel]
    except KeyError:
        assert i <= j
        try:
            d["max"] += 1
        except KeyError:
            d["max"] = 1

        ret = d["max"]
        if not i in d:
            d[i] = dict()
        if not j in d[i]:
            d[i][j] = dict()
        assert not baserel in d[i][j]
        d[i][j][baserel] = ret
        return ret

def base_relation_to_start_end_points(x,y,b):
    conj = set() # literals
    if b == '=':
        conj.add( literal('p',x,'-','=',y,'-') )
        conj.add( literal('p',x,'+','=',y,'+') )
        ###### complete ...
        conj.add( literal('p',x,'-','<=',y,'-') )
        conj.add( literal('p',x,'-','>=',y,'-') )
        conj.add( literal('p',x,'+','<=',y, '+') )
        conj.add( literal('p',x,'+','>=',y, '+') )
        conj.add( literal('p',x,'-','<=',y,'+') )
        conj.add( literal('p',y,'-','<=',x,'+') )

        conj.add( literal('n',x,'-','=',y,'+') )
        conj.add( literal('n',x,'+','=',y,'-') )
    elif b == '<':
        conj.add( literal('p',x,'+','<=',y,'-') )
        conj.add( literal('n',x,'+','=',y,'-') )
        ###### complete ...
        conj.add( literal('p',x,'+','<=',y,'+') )
        conj.add( literal('n',x,'+','=',y,'+') )
        conj.add( literal('p',x,'-','<=',y,'-') )
        conj.add( literal('n',x,'-','=',y,'-') )
        conj.add( literal('p',x,'-','<=',y,'+') )
        conj.add( literal('n',x,'-','=',y,'+') )

#        conj.add( ('p',x,'+','<=',y, '+') )
#        conj.add( ('n',x,'+','=',y,'+') )
    elif b == '>':
        return base_relation_to_start_end_points(y,x,'<')
    elif b == 'm':
        conj.add( literal('p',x,'+','=',y,'-') )
    elif b == 'mi':
        return base_relation_to_start_end_points(y,x,'m')
    elif b == 'd':
        conj.add( literal('p',y,'-','<=',x,'-') )
        conj.add( literal('n',y,'-','=',x,'-',) )
        conj.add( literal('p',x,'+','<=',y,'+') )
        conj.add( literal('n',x,'+','=',y,'+') )
        ###### complete ...
        conj.add( literal('p',y,'-','<=',x,'+') )
        conj.add( literal('n',y,'-','=',x,'+') )
        conj.add( literal('p',x,'-','<=',y,'+') )
        conj.add( literal('n',x,'-','=',y,'+') )
    elif b == 'di':
        return base_relation_to_start_end_points(y,x,'d')
    elif b == 's':
        conj.add( literal('p',x,'-','=',y,'-') )
        conj.add( literal('p',x,'+','<=',y,'+') )
        conj.add( literal('n',x,'+','=',y,'+') )
    elif b == 'si':
        return base_relation_to_start_end_points(y,x,'s')
    elif b == 'f':
        conj.add( literal('p',x, '-','<=',y, '+') )
        conj.add( literal('n',x, '-','=', y, '+') )
        conj.add( literal('p',x, '+','=', y, '+') )
    elif b == 'fi':
        return base_relation_to_start_end_points(y,x,'f')
    elif b == 'o':
        conj.add( literal('p',y,'-','<=',x,'+') )
        conj.add( literal('n',y,'-','=',x,'+') )
        conj.add( literal('p',x,'+','<=',y,'+') )
        conj.add( literal('n',x,'+','=', y,'+') )

        conj.add( literal('p',x,'-','<=',y,'-') )
        conj.add( literal('n',x,'-','=',y,'-') )

        conj.add( literal('p',x,'-','<=',y,'+') )
        conj.add( literal('n',x,'-','=',y,'+') )
    elif b == 'oi':
        return base_relation_to_start_end_points(y,x,'o')
    else: # unknown base relation
        assert False

    # well-formed intervals
    conj.add( literal('p',x,'-','<=',x,'+') )
    conj.add( literal('n',x,'-','=',x,'+') )
    conj.add( literal('p',y,'-','<=',y,'+') )
    conj.add( literal('n',y,'-','=',y,'+') )

    assert conj

    return conj

class literal:
#    def __init__(self, n, a, r, b): # TODO rewrite signature too simple points (not interval start/end shit)
    def __init__(self, n, a, s1, r, b, s2):
        assert n != 'n' or r == "="
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

def simplify_cnf(cnf): # subsumption testing, unit_propagation
    print "\tSimplify CNF:", len(cnf), " -> ",

    subsumptions = 0
    simplifications = 0
    ups = 0

    while True:
        done = True
        clauses = list(cnf)
        clauses.sort(key=lambda x: len(x)) # optimizing ...
        for clause_a in clauses:
            if not done:
                break
            for clause_b in clauses:
                if not clause_a == clause_b and clause_a <= clause_b:
                    cnf.remove(clause_b)
                    subsumptions += 1
                    done = False
            for l in clause_a:
                if not done:
                    break
                for l2 in clause_a:
                    if l.get_atom() == l2.get_atom() and l.is_positive() ^ l2.is_positive():
                        cnf.remove(clause_a)
                        simplifications += 1
                        done = False
                        break

            if not done:
                break

            # UP
            if len(clause_a) == 1:
                l = list(clause_a)[0]
                if l.r != '=':
                    continue
                nl = l.get_negation()
                for clause_b in clauses:
                    if not clause_a == clause_b and nl in clause_b:
                        ups += 1
                        cnf.remove(clause_b)
                        new = frozenset([t for t in clause_b if not t == nl])

#                        __print_nf([clause_a])
#                        __print_nf([clause_b])

                        assert new # otherwise contradiction...
                        assert not nl in new
                        cnf.add(new)
                        done = False
#                        assert False # theory UP unnecessary ...
                        break

        if done:
            print len(cnf), "(subs.: %d, simpl: %d, up: %d)" % (subsumptions, simplifications, ups)
            return cnf

def __print_nf(formula):
    print "{",
    for x in formula:
        print "{",
        for a in x:
            print a,
        print "}",
    print "}"

def background_theory(clause):
    cl = set(clause)

    done = False
    while not done: # TODO: loop potentially uninteresting :/
        done = True
        for l1 in cl:
            if not done:
                break
            for l2 in cl:
                if l1 == l2:
                    continue
                if (l1.x,l1.s1,l1.y,l1.s2) == (l2.x,l2.s1,l2.y,l2.s2) and \
                    l1.r == '<=' and l2.r == '>=':
                    return None
                # transitivity on well-formed intervals
                if (l1.x, l1.y) != (l2.x,l2.y):
                    continue
                if (l1.s1, l2.s1) == ('+','-') and \
                    l1.s2 == l2.s2 == '-' and l1.r == ">=" and l2.r == "<=":
                    return None
                if (l1.s1, l2.s1) == ('-','+') and \
                    l1.s2 == l2.s2 == '+' and l1.r == "<=" and l2.r == ">=":
                    return None
                if (l1.s2, l2.s2) == ('+','-') and \
                    l1.s1 == l2.s1 == '+' and l1.r == "<=" and l2.r == ">=":
                    return None
                if (l1.s2, l2.s2) == ('+','-') and \
                    l1.s1 == l2.s1 == '-' and l1.r == "<=" and l2.r == ">=":
                    return None

                if (l1.s1, l2.s1) == ('+','-') and (l1.s2, l2.s2) == ('-','+') and \
                    l1.r == ">=" and l2.r == "<=":
                        return None
    return frozenset(cl)

def nebel_buerckert_ordhorn(x, y, relation, d): # build CNF
    clauses = set()
    print "Encode", relation, "..."

    disj = set()
    for b in relation:
        conj = base_relation_to_start_end_points('x','y',b)
        disj.add(frozenset(conj))

    print "\tDNF:\t",
    __print_nf(disj)

    import itertools
    for element in itertools.product(*disj):
        s = background_theory(element)
        if s:
            clauses.add(s)
#    print "\tF-CNF:\t",
#    __print_nf(clauses)

    reduced = simplify_cnf(clauses)
    assert reduced
    for e in reduced:
        assert e

    print "\tCNF:\t",
    __print_nf(reduced)

    return reduced

def encode(x, s1, y, s2, rel, d):
    if x <= y:
        return encodeDict(x, y, s1+s2+rel, d)
    if x > y:
        srel = '<='
        if rel == '<=':
            srel = '>='
        elif rel == '=':
            srel = '='
        else:
            assert rel == '>='
        return encodeDict(y, x, s2+s1+srel, d)

def nebel_buerckert_encode_variables(instance, CSP, max_node, cgraph, boolvars):
    ### DEBUG CODE ###
    flines = open('allen/hornalg', 'r')
    lines = flines.readlines()
    flines.close()

    fails = 0
    for i, l in enumerate(lines):
        t = l[2:-3].split(' ')
        if t == ['']: # empty relation
            continue
        print "[%3d/%3d %3.2f]" % (i, len(lines), float(i)/float(len(lines))), l, t
        cnf = nebel_buerckert_ordhorn(0, 1, t, boolvars)
        # assert horn encoding
        for c in cnf:
            if len([l for l in c if l.is_positive()] ) > 1:
                __print_nf([c])
                raise SystemExit("[ERROR]: ... is not a horn clause :(")
                fails += 1
                print "[ERROR]: ... is not a horn clause :("
                print fails, "errors so far ..."
                break
    print "Failed: ", fails
    assert False

    # full ORD theory
    for i in xrange(max_node+1):
        for j in xrange(max_node+1):
            if i != j and (not (i, j) in cgraph or not (j, i) in cgraph):
                continue
            for s1 in [ '-', '+' ]:
                for s2 in [ '-', '+' ]:
                    encode(i, s1, j, s2, '<=', boolvars)
                    encode(i, s1, j, s2, '=', boolvars)

    for i in xrange(max_node+1):
        for j in xrange(max_node+1):
            if i != j and (not (i, j) in cgraph or not (j, i) in cgraph):
                continue
            #2
            for s1 in [ '-', '+' ]:
                instance.add_clause( [ encode(i,s1,j,s1,'<=',boolvars) ] )

            #3
            for s1 in [ '-', '+' ]:
                for s2 in [ '-', '+' ]:
                    instance.add_clause( [ -1 * encode(i,s1,j,s2,'<=',boolvars), -1 * encode(i,s1,j,s2,'>=',boolvars), encode(i,s1,j,s2,'=',boolvars) ] )
            #4 / 5
            for s1 in [ '-', '+' ]:
                for s2 in [ '-', '+' ]:
                    instance.add_clause( [ -1 * encode(i,s1,j,s2,'=',boolvars), encode(i,s1,j,s2,'<=',boolvars) ] )
                    instance.add_clause( [ -1 * encode(i,s1,j,s2,'=',boolvars), encode(i,s1,j,s2,'>=',boolvars) ] )

            for k in xrange(max_node+1):
                if j != k and i != k and (not (j, k) in cgraph or not (i, k) in cgraph):
                    continue

                #1
                for s1 in [ '-', '+' ]:
                    for s2 in [ '-', '+' ]:
                        instance.add_clause( [ -1 * encode(i,s1,j,s2,'<=',boolvars), -1 *  encode(j,s1,k,s2,'<=',boolvars), encode(i,s1,k,s2,'<=', boolvars)] )

    print "DONE ORD-Theory"

    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not (i, j) in cgraph:
                continue

            r = CSP[i][j]

            for clause in nebel_buerckert_ordhorn(i, j, r, boolvars):
                instance.add_clause( clause )

def __is_horn(cnf):
    for c in cnf:
        if len([l for l in c if l.is_positive()] ) > 1:
            return False
    return True

if __name__ == '__main__':
    print "[Nebel/Bürckert] Generate map \pi for all relations"

    boolvars = None

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

    ##### TODO the following ######

    signature = [ '=', '<', '>', 's', 'si', 'f', 'fi', 'd', 'di', 'm', 'mi', 'o', 'oi' ]
    prod = [ ]
    for i in xrange(0,13):
        prod.append(signature)


    import itertools
    import string
    for relation in itertools.product(*prod):
        relation_s = frozenset(relation)
        cnf = nebel_buerckert_ordhorn(0,1, relation_s, boolvars)
        __print_nf(cnf)
        cnf.remove( frozenset([literal('p', 'x', '-', '<=', 'x', '+')]) )
        cnf.remove( frozenset([literal('n', 'x', '-', '=', 'x', '+')]) )
        cnf.remove( frozenset([literal('p', 'y', '-', '<=', 'y', '+')]) )
        cnf.remove( frozenset([literal('n', 'y', '-', '=', 'y', '+')]) )
        print "x ( "+string.join(list(relation_s))+" ) y ::",
        __print_nf(cnf)
        print "Is ordhorn:", __is_horn(cnf), "Is in known ordhorn relations:", relation_s in ordhorn
        assert (__is_horn(cnf) and relation_s in ordhorn) or (not __is_horn(cnf) and not relation_s in ordhorn)
