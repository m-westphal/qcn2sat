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

__VERSION="0.2 alpha"

import copy, re, sys, string
import collections, bz2

class cnf_output:
    def __init__(self, only_estimate_size=False):
        self.only_estimate_size = only_estimate_size
        self.variables = 0
        self.bzip2 = bz2.BZ2Compressor(9)
        self.clauses_bz2 = collections.deque()
        self.fd = sys.stdout
        self.number_of_clauses = 0
        if self.only_estimate_size:
            self.bytes = 0

    def add_clause(self, clause):
        self.number_of_clauses += 1
        self.variables = max( max([abs(l) for l in clause]), self.variables)
        cl = self.encode_clause(clause)
        if only_estimate_size:
            self.bytes += len(cl)
        else:
            chunk = self.bzip2.compress(cl)
            if chunk:
                self.clauses_bz2.append(chunk)

    def generate_header(self):
        assert self.variables > 0
        assert self.number_of_clauses > 0
        header = "p cnf %d %d\n" % (self.variables, self.number_of_clauses)
        return header

    def encode_clause(self, c):
        """turn clause into string"""
        clause = [`v` for v in c]  # turn into strings
        return string.join(clause+['0\n'])

    def flush(self):
        """output CNF; invalidates class content"""
        if self.only_estimate_size:
            size = len(self.generate_header())+self.bytes
            print "Constructed %d variables and %d clauses" % (self.variables, self.number_of_clauses)
            print "Computed %d bytes (%d MiB) of CNF formulae" % (size, size/1024**2)
        else:
            self.clauses_bz2.append(self.bzip2.flush())
            del self.bzip2

            self.fd.write(self.generate_header())
            decomp = bz2.BZ2Decompressor()
            while self.clauses_bz2:
                chunk = self.clauses_bz2.popleft()
                self.fd.write(decomp.decompress(chunk))
            del decomp

class QCN:
    def __init__(self, signature):
        self.size = 0
        self.signature = frozenset(signature)
        s_sign = list(signature)
        s_sign.sort()
        self.universal = s_sign
        self.constraints = dict()

        self.graph = None

    def add(self, i, j, relation):
        self.size = max(self.size, max(i,j)+1)
        assert i < j
        for b in relation:
            if not b in self.signature:
                raise SystemExit("Base relation not in given signature\n")

        idx = (i,j)
        old = self.signature
        if idx in self.constraints:
            old = frozenset(self.constraints[idx])
        relation_sort = list(frozenset(relation) & old)
        relation_sort.sort()

        self.constraints[idx] = relation_sort

    def get(self, i, j):
        try:
            return self.constraints[(i,j)]
        except KeyError:
            return self.universal

    def iterate_strict_triangle(self):
        if not self.graph:
            for i in xrange(0, self.size):
                for j in xrange(i+1, self.size):
                    yield i, j
        else:
            iterate = [ (i, j) for (i, j) in self.graph if i < j ]
            iterate.sort()
            for (i, j) in iterate:
                yield i, j
    def iterate_strict_triples(self):
        """iterate i < j < k triples"""
        if not self.graph:
            for i in xrange(0, self.size):
                for j in xrange(i+1, self.size):
                    for k in xrange(j+1, self.size):
                        yield i, j, k
        else:
            iterate = [ (i, j) for (i, j) in self.graph if i < j ]
            iterate.sort()

            nb = dict()
            for i in xrange(self.size):
                nb[i] = set()

            for (i, j) in iterate:
                nb[i].add(j)

            for (i, j) in iterate:
                for k in nb[i] & nb[j]:
                    yield i, j, k

class PropositionalAtoms:
    def __init__(self):
        self.names = dict()
        self.last_used = 0
    
    def encode(self, i, j, baserel):
        """assign a boolean atom (id number) to baserel in R_ij"""

        try:
            return self.names[i][j][baserel]
        except KeyError:
            assert i <= j
            self.last_used += 1

            if not i in self.names:
                self.names[i] = dict()
            if not j in self.names[i]:
                self.names[i][j] = dict()
            self.names[i][j][baserel] = self.last_used
            return self.last_used

def readCompTable(calculus):
    table = { }
    ALL_RELATIONS = [ ]

    lines = open(calculus, 'r')
    for l in lines:
        extract = re.search('^(.*):(.*)::[ ]*\((.*)\)$', l)
        assert(extract)
        left = extract.group(1).strip()
        right = extract.group(2).strip()
        supp = extract.group(3).strip()
        table[left + " " + right] = frozenset(supp.split())
        if not left in ALL_RELATIONS:
            ALL_RELATIONS.append(left)
        if not right in ALL_RELATIONS:
            ALL_RELATIONS.append(right)
    lines.close()

    return table, frozenset(ALL_RELATIONS)

def readGQRCSPstdin(signature):
    data = QCN(signature)

    lines = sys.stdin.readlines()
    for l in lines:
        res = re.search('^[ ]*([0-9]*)[ ]*([0-9]*) \((.*)\)', l)
        if res:
            x = int(res.group(1))
            y = int(res.group(2))
            assert 0 <= x < y
            rel = res.group(3).strip().split(" ")
            if not rel:
                return None
            for b in rel:
                if not b in signature:
                    raise SystemExit("Calculus signature does not match CSP")

            if frozenset(rel) != signature:  # ignore universal statements
                data.add(x, y, rel)

    return data


def directDomEncoding(instance, qcn, atoms):
    """build (var,val) as bool variables with ALO/AMO clauses"""

    for i, j in qcn.iterate_strict_triangle():
        rel = qcn.get(i, j)
        alo = [ atoms.encode(i, j, br) for br in rel ]
        instance.add_clause(alo)

        for x in xrange(len(rel)):
            br1 = rel[x]
            for y in xrange(x+1,len(rel)):
                br2 = rel[y]
                amo = [ -1 * atoms.encode(i, j, br1), -1 * atoms.encode(i, j, br2) ]
                instance.add_clause(amo)

def binra_support(qcn, comptable, out):
    atoms = PropositionalAtoms()

    directDomEncoding(out, qcn, atoms)

    for i, j, k in qcn.iterate_strict_triples():
        r_ij = qcn.get(i, j)
        r_ik = qcn.get(i, k)
        r_jk = qcn.get(j, k)
        for br1 in r_ij:
            not_b_ij = -1 * atoms.encode(i, j, br1)
            for br2 in r_jk:
                intersection = list(frozenset(r_ik) & comptable[br1 + " " + br2])
                intersection.sort()

                cl = [ not_b_ij, -1 * atoms.encode(j, k, br2) ]
                cl += [ atoms.encode(i, k, br) for br in intersection ]
                out.add_clause(cl)

def binra_direct(qcn, comptable, out):
    atoms = PropositionalAtoms()

    directDomEncoding(out, qcn, atoms)

    for i, j, k in qcn.iterate_strict_triples():
        r_ij = qcn.get(i, j)
        r_ik = qcn.get(i, k)
        r_jk = qcn.get(j, k)

        for br1 in r_ij:
            not_b_ij = -1 * atoms.encode(i, j, br1)
            for br2 in r_jk:
                intersection = list(frozenset(r_ik) & comptable[br1 + " " + br2])
                intersection.sort()

                cl = [ not_b_ij, -1 * atoms.encode(j, k, br2) ]
                for br in signature:
                    if not br in intersection and br in r_ik:
                        cl2 = cl + [ -1 * atoms.encode(i, k, br) ]
                        out.add_clause(cl2)

def lexBFS(vertices, edges):
    assert vertices
    assert edges

    order = dict()

    label = dict()
    for v in vertices:
        label[v] = [ ]
    for i in xrange(len(vertices), 0, -1):
        todo = [ v for v in vertices if not v in order ]
        todo.sort(key=lambda x: label[x])
        todo.reverse()
        assert label[todo[0]] >= label[todo[-1]]
        v = todo[0]
        order[v] = i
        for w in edges[v]:
            if not w in order:
                label[w].append(i)

    return order

def eliminationGame(vertices, edges, order):
    from itertools import product
    import copy

    new_edges = [ edges.copy() ] # G^0

    queue = list(vertices)
    queue.sort(key=lambda x: order[x]) # lowest weight first
    assert order[queue[0]] <= order[queue[1]]

    for v in queue:
        tmp = copy.deepcopy(new_edges[-1]) # G^{i-1}

        # Turn v into a clique in tmp
        for x, y in product(new_edges[-1][v], new_edges[-1][v]):
            if x == y:
                continue
            tmp[x].add(y)
            tmp[y].add(x)
        # remove v from G^i
        for x in tmp:
            tmp[x].discard(v) # remove edges to v if present
        del tmp[v] # remove v itself
        new_edges.append(tmp) # add G^i

    final = dict( [ (v, set()) for v in vertices ] )
    for graph in new_edges[:-1]:
        for v in graph:
            final[v] |= graph[v]

    ret = set()
    for v in vertices:
        ret |= set( [ (v, x) for x in final[v] ] )
    return frozenset(ret)

def check_options():
    from argparse import ArgumentParser

    add_inf = 'Notes: (1) the script does stream processing: a qualitative' \
              ' CSP in GQR format is read from stdin, clauses written' \
              ' to stdout. ' \
              '(2) Syntactical processing only, chosen options may result' \
              ' in unsound output.'
    copyright = 'Copyright (C) 2009-2013 Matthias Westphal.' \
                ' This program comes with ABSOLUTELY NO WARRANTY.' \
                ' This is free software, and you are welcome to redistribute it' \
                ' under certain conditions; see `GPL-3\' for details'

    parser = ArgumentParser(
        description='qcsp2sat.py: convert QCNs to CNF formulae (version %s)' % __VERSION,
        epilog=add_inf+" "+copyright)

    parser.add_argument('--only-estimate', action='store_true',
        help='only calculate size of CNF; do not store/return clauses')

    graph_type_inf = '; partitioning may be unsound for several calculi.'
    parser.add_argument('--graph-type', metavar='STR', nargs=1, default=False,
        required = True, type=str, choices=['complete', 'lexbfs'],
        help='constraint graph type [%(choices)s]'+graph_type_inf)
    encoding_inf = '; see \"Towards An Efficient SAT Encoding for' \
                   ' Temporal Reasoning\", Pham et al.,' \
                   ' \"Reasoning about Temporal Relations: A Maximal' \
                   ' Tractable Subclass\", Nebel and Bürckert.'
    parser.add_argument('--encoding', metavar='STR', nargs=1, default=False,
        required=True, type=str,
        choices=['support', 'direct', 'ord-clauses',
                'support-pa', 'direct-pa'],
        help='encoding [%(choices)s]'+encoding_inf)
    parser.add_argument('GQR_COMPOSITION_TABLE_FILE')

    result = parser.parse_args()

    return result.only_estimate, result.encoding[0], result.graph_type[0], result.GQR_COMPOSITION_TABLE_FILE

if __name__ == '__main__':
    only_estimate_size, clause_type, graph_type, ct_filename = check_options()

    comptable, signature = readCompTable(ct_filename)
    qcn = readGQRCSPstdin(signature)

    if qcn.size == 0:  # no constraints read; assume problem was unsatisfiable
        print "p cnf 1 2"
        print "1 0"
        print "-1 0"
        raise SystemExit()

    if graph_type == 'lexbfs':
            vertices = set( [ t for (t, _) in qcn.constraints.keys() ] +
                            [ t for (_, t) in qcn.constraints.keys() ] )
            edges = dict( [ (v, set()) for v in vertices ] )
            for (i, j) in qcn.constraints.keys():
                edges[i].add(j)
                edges[j].add(i)

            order = lexBFS(vertices, edges)
            qcn.graph = eliminationGame(vertices, edges, order)

    instance = cnf_output(only_estimate_size)
    if clause_type == 'support':
        binra_support(qcn, comptable, instance)
    elif clause_type == 'direct':
        binra_direct(qcn, comptable, instance)
    elif clause_type == 'ord-clauses':
        import allen
        allen.nebel_buerckert_encode_variables(qcn, instance)
    elif clause_type == 'support-pa':
        import allen
        allen.pham_support_pt_encode(qcn, instance)
    elif clause_type == 'direct-pa':
        import allen
        allen.pham_direct_pt_encode(qcn, instance)
    instance.flush()  # note, invalidates content as well
