#! /usr/bin/env python

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

def base_relation_to_start_end_points(x, y, b, d):
    conj = set() # literals
    if b == '=':
        conj.add( encode(x, '-', y, '-', '=', d) )
        conj.add( encode(x, '+', y, '+', '=', d) )
        ###### complete ...
        conj.add( encode(x, '-', y, '-', '<=', d) )
        conj.add( encode(x, '+', y, '+', '<=', d) )
        conj.add( encode(x, '-', y, '-', '>=', d) )
        conj.add( encode(x, '+', y, '+', '>=', d) )
        conj.add( encode(x, '-', y, '+', '<=', d) )
        conj.add( encode(y, '-', x, '+', '<=', d) )
    elif b == '<':
        conj.add( encode(x, '+', y, '-', '<=', d) )
        conj.add( -1 * encode(x, '+', y, '-', '=', d) )
        ###### complete ...
#        conj.add( encode(x, '-', y, '-', '<=', d) )
#        conj.add( -1 * encode(x, '-', y, '-', '=', d) )
#        conj.add( encode(x, '-', y, '+', '<=', d) )
#        conj.add( -1 * encode(x, '-', y, '+', '=', d) )
        conj.add( encode(x, '+', y, '+', '<=', d) )
        conj.add( -1 * encode(x, '+', y, '+', '=', d) )
    elif b == '>':
        return base_relation_to_start_end_points(y,x,'<',d)
    elif b == 'm':
        conj.add( encode(x, '+', y, '-', '=', d) )
    elif b == 'mi':
        return base_relation_to_start_end_points(y,x,'m',d)
    elif b == 'd':
        conj.add( encode(y, '-', x, '-', '<=', d) )
        conj.add( -1 * encode(y, '-', x, '-', '=', d) )
        conj.add( encode(x, '+', y, '+', '<=', d) )
        conj.add( -1 * encode(x, '+', y, '+', '=', d) )
        ###### complete ...
        conj.add( encode(y, '-', x, '+', '<=', d) )
        conj.add( -1 * encode(y, '-', x, '+', '=', d) )
        conj.add( encode(x, '-', y, '+', '<=', d) )
        conj.add( -1 * encode(x, '-', y, '+', '=', d) )
    elif b == 'di':
        return base_relation_to_start_end_points(y,x,'d',d)
    elif b == 's':
        conj.add( encode(x, '-', y, '-', '=', d) )
        conj.add( encode(x, '+', y, '+', '<=', d) )
        conj.add( -1 * encode(x, '+', y, '+', '=', d) )
    elif b == 'si':
        return base_relation_to_start_end_points(y,x,'s',d)
    elif b == 'f':
        conj.add( encode(x, '-', y, '+', '<=', d) )
        conj.add( -1 * encode(x, '-', y, '+', '=', d) )
        conj.add( encode(x, '+', y, '+', '=', d) )
    elif b == 'fi':
        return base_relation_to_start_end_points(y,x,'f',d)
    elif b == 'o':
        conj.add( encode(y, '-', x, '+', '<=', d) )
        conj.add( -1 * encode(y, '-', x, '+', '=', d) )
        conj.add( encode(x, '+', y, '+', '<=', d) )
        conj.add( -1 * encode(x, '+', y, '+', '=', d) )
        ##### complete ...
#        conj.add( encode(x, '+', y, '+', '<=', d) )
#        conj.add( -1 * encode(x, '+', y, '+', '=', d) )
#        conj.add( encode(x, '-', y, '-', '<=', d) )
#        conj.add( -1 * encode(x, '-', y, '+', '=', d) )
    elif b == 'oi':
        return base_relation_to_start_end_points(y,x,'o',d)
    else: # unknown base relation
        assert False

    conj.add( encode(x, '-', x, '+', '<=', d) )
    conj.add( -1 * encode(x, '-', x, '+', '=', d) )
    conj.add( encode(y, '-', y, '+', '<=', d) )
    conj.add( -1 * encode(y, '-', y, '+', '=', d) )

    # contradiction free ...
    assert len(conj) == len( set([abs(l) for l in conj] ) )
    assert conj

    return conj

def unit_resolution(cnf): # fails upon conflict
    # subsumption testing
    for x in cnf:
        for y in cnf:
            if x != y and x <= y:
                cnf.remove(y)
#                print "\tRemove", y, "cause of", x
                assert cnf
                return unit_resolution(cnf)
        double = set([abs(t) for t in x if -1*t in x])
        if double:
            t = frozenset([ t for t in x if abs(t) not in double ])
            cnf.remove(x)
            if not t:
                assert cnf
                return unit_resolution(cnf)
#            print "\tWds.", x, "replace with", t
            return unit_resolution(cnf | set([t]))
    return cnf
    units = frozenset( [ list(u)[0] for u in cnf if len(u) == 1 ] )
    for u in units:
        for v in units:
            assert u == v or abs(u) != abs(v)
    non_units = [ nu for nu in cnf if len(nu) > 1 ]

    new = set()
    done = True
    for c in non_units:
        nc = frozenset([ l for l in c if not (-1 * l) in units ])
        if nc != c:
            print "Minimizing:", list(c), "to", list(nc), "\t\tunits", [ t for t in units ]
            done = False
        assert nc
        new.add(nc)

    ncnf = frozenset([ frozenset([t]) for t in units] + [t for t in new])
    assert ncf
    if done:
        return ncnf
    else:
        return unit_resolution(ncnf)

def nebel_buerckert_ordhorn(x, y, relation, d): # build CNF
    clauses = set()
    print "Encode", relation, "..."

    disj = set()
    for b in relation:
        conj = base_relation_to_start_end_points(x,y,b,d)
        disj.add(frozenset(conj))

    print "\tDNF:\t", [ list(e) for e in  disj ]

    import itertools
    for element in itertools.product(*disj):
        clauses.add( frozenset(element) )
    print "\tF-CNF:\t", [ list(e) for e in clauses ]

    reduced = unit_resolution(clauses)
    assert reduced

    print "\tCNF:\t", [ list(e) for e in reduced ]

    return [ list(e) for e in reduced ]

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

    for i, l in enumerate(lines):
        t = l[2:-3].split(' ')
        if t == ['']: # empty relation
            continue
        print "[%3d/%3d %3.2f]" % (i, len(lines), float(i)/float(len(lines))), l, t
        cnf = nebel_buerckert_ordhorn(0, 1, t, boolvars)
        # assert horn encoding
        for c in cnf:
            if len([t for t in c if t > 0] ) > 1:
                raise SystemExit("[ERROR]: "+str(c)+" is not a horn clause :(")
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
