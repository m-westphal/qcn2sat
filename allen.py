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
        assert i < j
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

def nebel_buerckert(constraints):
    for x, y, r in constraints:
        pass

def nebel_buerckert_ordhorn(x, y, relation, d): # build CNF
    clauses = [ ]

    disj = set()
    for b in relation:
        conj = set()
        conj.add( encode_wrap(x, x, '-', '+', '<=', d) )
        if b == '=':
            conj.add( encode_wrap(x, y, '-', '-', '=', d) )
            conj.add( encode_wrap(x, y, '-', '-', '=', d) )
            conj.add( encode_wrap(x, y, '-', '-', '=', d) )
        print b

    return clauses

def encode_wrap(x, y, s1, s2, rel, d):
    if x < y:
        return encodeDict(x, y, s1+s2+rel, d)
    if x > y:
        srel = '<='
        if rel == '<=':
            srel = '>='
        if rel == '=':
            srel = '='
        return encodeDict(y, x, s1+s2+srel, d)

def nebel_buerckert_encode_variables(instance, CSP, max_node, cgraph, boolvars):
    # full ORD theory
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not (i, j) in cgraph:
                continue
            for s1 in [ '-', '+' ]:
                for s2 in [ '-', '+' ]:
                    encodeDict(i, j, s1+s2+'<=', boolvars)
                    encodeDict(i, j, s1+s2+'=', boolvars)
                    encodeDict(i, j, s1+s2+'>=', boolvars)

    for i in xrange(max_node+1):
        for j in xrange(max_node+1):
            if i == j or not (i, j) in cgraph:
                continue
            #2
            for s1 in [ '-', '+' ]:
                instance.add_clause( [ encode_wrap(i,j,s1,s1,'<=',boolvars) ] )

            #3
            for s1 in [ '-', '+' ]:
                for s2 in [ '-', '+' ]:
                    instance.add_clause( [ -1 * encode_wrap(i,j,s1,s2,'<=',boolvars), -1 * encode_wrap(i,j,s1,s2,'>=',boolvars), encode_wrap(i,j,s1,s2,'=',boolvars) ] )
            #4 / 5
            for s1 in [ '-', '+' ]:
                for s2 in [ '-', '+' ]:
                    instance.add_clause( [ -1 * encode_wrap(i,j,s1,s2,'=',boolvars), encode_wrap(i,j,s1,s2,'<=',boolvars) ] )
                    instance.add_clause( [ -1 * encode_wrap(i,j,s1,s2,'=',boolvars), encode_wrap(i,j,s1,s2,'>=',boolvars) ] )

            for k in xrange(max_node+1):
                if j == k or i == k or not (j, k) in cgraph or not (i, k) in cgraph:
                    continue

                #1
                for s1 in [ '-', '+' ]:
                    for s2 in [ '-', '+' ]:
                        instance.add_clause( [ -1 * encode_wrap(i,j,s1,s2,'<=',boolvars), -1 *  encode_wrap(j,k,s1,s2,'<=',boolvars), encode_wrap(i,k,s1,s2,'<=', boolvars)] )

    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not (i, j) in cgraph:
                continue

            r = CSP[i][j]

            instance.add_clause( encode_wrap(i,j,'-','+','<=',boolvars) )
            instance.add_clause( encode_wrap(i,j,'-','+','<=',boolvars) )

            for c in nebel_buerckert_ordhorn(i, j, r, boolvars):
                instance.add_clause( c )
