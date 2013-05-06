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


from qcsp2sat import encodeDict

def readASPSolution(filename, signature):
    import re

    nogoods = []
    representation = dict()

    lines = open(filename,'r')
    for l in lines:
        if 'inf' in l:
            for inf in l.split('inf'):
                if inf == '':
                    continue
                inf = inf.strip()
                content = re.match(r'\(([\d]+),([\d]+),([\d]+),([\d]+),([\d]+),([\d]+)\)', inf)
                xz = (content.group(1), content.group(2))
                if xz[0] == '0':
                    xz = (1, content.group(2)) # NEGATION
                else:
                    xz = (-1, content.group(2)) # NEGATION
                xy = (content.group(3), content.group(4))
                if xy[0] == '0':
                    xy = (-1, content.group(4))
                else:
                    xy = (1, content.group(4))
                yz = (content.group(5), content.group(6))
                if yz[0] == '0':
                    yz = (-1, content.group(6))
                else:
                    yz = (1, content.group(6))
                nogoods.append( (xz,xy,yz) ) # TODO
        if 'dec' in l:
            for dec in l.split('dec'):
                if dec == '':
                    continue
                dec = dec.strip()
                content = re.match(r'\(([\d]+),([\D]+),([\d]+)\)', dec)
                negation, br, atom = (content.group(1), content.group(2)[1:], content.group(3))
                if negation == '0':
                    negation = -1
                elif negation == '1':
                    negation = 1
                else:
                    assert False

                try:
                    representation[br].append( (negation, atom) )
                except KeyError:
                    representation[br] = [ (negation, atom) ]

    lines.close()
    if set(representation.keys()) == set(signature):
        nogoods.sort()
        return nogoods, representation

    return None, None

def intDomEncoding(instance, qcn, boolvars, nogoods, representation):
    """build (var,val) as bool variables with ALO/AMO/FOR clauses"""
    import itertools

    nr_atoms = None  # number of propositional atoms in the decomposition
    for br in qcn.universal:
        t = len(representation[br])
        if nr_atoms is None:
            nr_atoms = t
        assert t == nr_atoms

    for i, j in qcn.iterate_strict_triangle():
        r = qcn.get(i,j)
        # forbidden clauses
        for m in itertools.product([-1,1],repeat=nr_atoms):  # all models
            is_allowed = False
            for br in qcn.universal:
                v = representation[br]
                v.sort(key=lambda x: x[1])
                t = tuple( [ n for (n, _) in v ] )
                if t == m and br in r:
                    is_allowed = True
                    break
            if not is_allowed:
                clause = [ -1 * n * encodeDict(i, j, 'atom'+str(a), boolvars) for (a,n) in enumerate(m) ]
                instance.add_clause(clause)

def writeSATint(qcn, comptable, out):
    boolvars = dict()

    nogoods = [ ]
    representation = dict()

    from os import path, listdir

    for f in listdir('data'):
        if f.endswith('.das'):
            (nogoods, representation) = readASPSolution(path.join('data',f), qcn.signature)
            if nogoods and representation:
                break
    if not representation:
        raise SystemExit('No syntactic interpretation found!')

    intDomEncoding(out, qcn, boolvars, nogoods, representation)

    for i, j, k in qcn.iterate_strict_triples():
        for xz, xy, yz in nogoods:
            clause = [ -1 * xy[0] * encodeDict(i, j, 'atom'+xy[1], boolvars) ]
            clause +=[ -1 * yz[0] * encodeDict(j, k, 'atom'+yz[1], boolvars) ]
            clause +=[ -1 * xz[0] * encodeDict(i, k, 'atom'+xz[1], boolvars) ]
            out.add_clause(clause)

