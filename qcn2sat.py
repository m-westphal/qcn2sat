#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Main script file."""

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

__VERSION = "1"

import collections, bz2

class CNFOutput:
    """CNF in memory."""
    def __init__(self, only_estimate_size=False):
        import sys
        self.only_estimate_size = only_estimate_size
        self.variables = 0
        self.bzip2 = bz2.BZ2Compressor(9)
        self.clauses_bz2 = collections.deque()
        self.filedescriptor = sys.stdout
        self.number_of_clauses = 0
        if self.only_estimate_size:
            self.bytes = 0

    def add_clause(self, clause):
        """Add clause to CNF"""
        self.number_of_clauses += 1
        self.variables = max( max([abs(l) for l in clause]), self.variables)
        # turn into strings
        cl_str = ' '.join([`l` for l in clause]+['0\n']) #pylint: disable=W0333
        if self.only_estimate_size:
            self.bytes += len(cl_str)
        else:
            chunk = self.bzip2.compress(cl_str)
            if chunk:
                self.clauses_bz2.append(chunk)

    def generate_header(self):
        """Return DIMACS header for CNF in current state"""
        assert self.variables > 0
        assert self.number_of_clauses > 0
        header = "p cnf %d %d\n" % (self.variables, self.number_of_clauses)
        return header

    def flush(self):
        """output CNF; invalidates class content"""
        if self.only_estimate_size:
            size = len(self.generate_header())+self.bytes
            print "Constructed %d variables and %d clauses" % (
                self.variables, self.number_of_clauses)
            print "Computed %d bytes (%d MiB) of propositional CNF" % (
                size, size/1024**2)
        else:
            self.clauses_bz2.append(self.bzip2.flush())
            del self.bzip2

            self.filedescriptor.write(self.generate_header())
            decomp = bz2.BZ2Decompressor()
            while self.clauses_bz2:
                chunk = self.clauses_bz2.popleft()
                self.filedescriptor.write(decomp.decompress(chunk))
            del decomp

class QCN:
    """Qualitative Constraint Network (restricted to arcs i < j)"""
    def __init__(self, signature):
        self.size = 0
        self.signature = frozenset(signature)
        s_sign = list(signature)
        s_sign.sort()
        self.universal = s_sign
        self.constraints = dict()

        self.graph = None

    def add(self, i, j, relation):
        """"Add a constraint (i < j)"""
        self.size = max(self.size, max(i, j)+1)
        assert i < j
        for base_rel in relation:
            if not base_rel in self.signature:
                raise SystemExit("Base relation not in given signature\n")

        idx = (i, j)
        old = self.signature
        if idx in self.constraints:
            old = frozenset(self.constraints[idx])
        relation_sort = list(frozenset(relation) & old)
        relation_sort.sort()

        self.constraints[idx] = relation_sort

    def get(self, i, j):
        """Read constraint on (i,j); always returns a relation."""
        try:
            return self.constraints[(i, j)]
        except KeyError:
            return self.universal

    def is_2_consistent(self):
        """Test 2-consistency"""
        for i, j in self.iterate_strict_triangle():
            if not self.get(i, j):
                return False
        return True

    def iterate_strict_triangle(self):
        """Iterate all pairs i < j on current primal constraint graph."""
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

            neighb = dict()
            for i in xrange(self.size):
                neighb[i] = set()

            for (i, j) in iterate:
                neighb[i].add(j)

            for (i, j) in iterate:
                for k in neighb[i] & neighb[j]:
                    yield i, j, k

class PropositionalAtoms:  # pylint: disable=R0903
    """Dictionary enumerating variable strings."""
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

def read_comp_table(calculus):
    """Read an Allen-solver/GQR-format composition table"""
    import re

    table = { }
    all_relations = set()

    lines = open(calculus, 'r')
    for line in lines:
        extract = re.search('^(.*):(.*)::[ ]*\((.*)\)$', line)
        assert(extract)
        left = extract.group(1).strip()
        right = extract.group(2).strip()
        supp = extract.group(3).strip()
        table[left + " " + right] = frozenset(supp.split())
        all_relations.add(left)
        all_relations.add(right)
    lines.close()

    return table, frozenset(all_relations)

def read_gqr_csp_stdin(signature):
    """Read an ALlen-solver/GQR-format CSP from input"""
    import sys, re

    data = QCN(signature)

    lines = sys.stdin.readlines()
    for line in lines:
        res = re.search('^[ ]*([0-9]*)[ ]*([0-9]*) \((.*)\)', line)
        if res:
            i = int(res.group(1))
            j = int(res.group(2))
            assert 0 <= i < j
            rel = res.group(3).strip().split(" ")
            if not rel:
                return None
            for base_rel in rel:
                if not base_rel in signature:
                    raise SystemExit("Calculus signature does not match CSP")

            if frozenset(rel) != signature:  # ignore universal statements
                data.add(i, j, rel)

    return data


def direct_dom_encoding(instance, qcn, atoms):
    """build (var,val) as bool variables with ALO/AMO clauses"""

    for i, j in qcn.iterate_strict_triangle():
        rel = qcn.get(i, j)
        alo = [ atoms.encode(i, j, br) for br in rel ]
        instance.add_clause(alo)

        for idx1 in xrange(len(rel)):
            br1 = rel[idx1]
            for idx2 in xrange(idx1+1, len(rel)):
                br2 = rel[idx2]
                amo = [ -1 * atoms.encode(i, j, br1),
                    -1 * atoms.encode(i, j, br2) ]
                instance.add_clause(amo)

def binra_support(qcn, comptable, out): # pylint: disable=R0914
    """The support encoding by Pham et al."""
    atoms = PropositionalAtoms()

    direct_dom_encoding(out, qcn, atoms)

    for i, j, k in qcn.iterate_strict_triples():
        r_ij = qcn.get(i, j)
        r_ik = qcn.get(i, k)
        r_jk = qcn.get(j, k)
        for br1 in r_ij:
            not_b_ij = -1 * atoms.encode(i, j, br1)
            for br2 in r_jk:
                intersection = list(frozenset(r_ik) & comptable[br1 +" "+ br2])
                intersection.sort()

                clause = [ not_b_ij, -1 * atoms.encode(j, k, br2) ]
                clause += [ atoms.encode(i, k, br) for br in intersection ]
                out.add_clause(clause)

def binra_direct(qcn, comptable, out): # pylint: disable=R0914
    """The direct encoding by Pham et al."""
    atoms = PropositionalAtoms()

    direct_dom_encoding(out, qcn, atoms)

    for i, j, k in qcn.iterate_strict_triples():
        r_ij = qcn.get(i, j)
        r_ik = qcn.get(i, k)
        r_jk = qcn.get(j, k)

        for br1 in r_ij:
            not_b_ij = -1 * atoms.encode(i, j, br1)
            for br2 in r_jk:
                intersection = list(frozenset(r_ik) & comptable[br1 +" "+ br2])
                intersection.sort()

                clause = [ not_b_ij, -1 * atoms.encode(j, k, br2) ]
                for base_rel in qcn.universal:
                    if not base_rel in intersection and base_rel in r_ik:
                        cl2 = clause + [ -1 * atoms.encode(i, k, base_rel) ]
                        out.add_clause(cl2)

def lex_bfs(vertices, edges):
    """Compute LexBFS order of vertices"""
    assert vertices
    assert edges

    order = dict()

    label = dict()
    for vertex in vertices:
        label[vertex] = [ ]
    for i in xrange(len(vertices), 0, -1):
        todo = [ vertex for vertex in vertices if not vertex in order ]
        todo.sort(key=lambda x: label[x])
        todo.reverse()
        assert label[todo[0]] >= label[todo[-1]]
        vertex = todo[0]
        order[vertex] = i
        for vertex2 in edges[vertex]:
            if not vertex2 in order:
                label[vertex2].append(i)

    return order

def greedy_x(vertices, edges):
    """The greedyX algorithm (here for GFI)"""
    assert vertices
    assert edges

    order = dict()
    import copy
    h_v = copy.deepcopy(vertices)
    h_e = copy.deepcopy(edges)

    for i in xrange(len(vertices)):
        sigma = dict()
        for vertex in h_v:
            sigma[vertex] = 0
            for nb1 in h_e[vertex]:
                for nb2 in h_e[vertex]:
                    if nb1 == nb2:
                        continue
                    assert nb1 != vertex and nb2 != vertex
                    if not nb1 in h_e[nb2]:
                        sigma[vertex] += 1
        todo = [ v for v in h_v ]
        todo.sort(key=lambda x: sigma[x])
        assert sigma[todo[0]] <= sigma[todo[-1]]
        vertex = todo[0]
        order[vertex] = i

        for nb1 in h_e[vertex]:
            for nb2 in h_e[vertex]:
                if nb1 == nb2:
                    continue
                if not nb1 in h_e[nb2]:
                    h_e[nb2].add(nb1)
                    h_e[nb1].add(nb2)

        h_v.remove(vertex)
        for ngb in h_e[vertex]:
            h_e[ngb].remove(vertex)
        del h_e[vertex]

    return order

def elimination_game(vertices, edges, order): # pylint: disable=R0914
    """Run the elimination game"""
    from itertools import product
    import copy

    new_edges = [ edges.copy() ] # G^0

    queue = list(vertices)
    queue.sort(key=lambda x: order[x]) # lowest weight first
    assert order[queue[0]] <= order[queue[1]]

    for vertex in queue:
        tmp = copy.deepcopy(new_edges[-1]) # G^{i-1}

        # Turn v into a clique in tmp
        for nb1, nb2 in product(new_edges[-1][vertex], new_edges[-1][vertex]):
            if nb1 == nb2:
                continue
            tmp[nb1].add(nb2)
            tmp[nb2].add(nb1)
        # remove v from G^i
        for ngb in tmp:
            tmp[ngb].discard(vertex) # remove edges to vertex if present
        del tmp[vertex] # remove vertex itself
        new_edges.append(tmp) # add G^i

    final = dict( [ (v, set()) for v in vertices ] )
    for graph in new_edges[:-1]:
        for vertex in graph:
            final[vertex] |= graph[vertex]

    ret = set()
    for vertex in vertices:
        ret |= set( [ (vertex, x) for x in final[vertex] ] )
    return frozenset(ret)

def check_options():
    """Parse options with assertions"""
    from argparse import ArgumentParser

    add_inf = 'Notes: (1) the script does stream processing: a qualitative' \
              ' CSP in GQR format is read from stdin, clauses written' \
              ' to stdout. ' \
              '(2) Syntactical processing only, chosen options may result' \
              ' in unsound output.'
    script_copyright = 'Copyright (C) 2009-2013 Matthias Westphal.' \
            ' This program comes with ABSOLUTELY NO WARRANTY.' \
            ' This is free software, and you are welcome to redistribute it' \
            ' under certain conditions; see `GPL-3\' for details'

    parser = ArgumentParser(
        description= 'qcn2sat.py: convert QCNs to propositional CNF' \
            ' (version %s)' % __VERSION,
        epilog=add_inf+" "+script_copyright)

    parser.add_argument('--only-estimate', action='store_true',
        help='only calculate size of CNF; do not store/return clauses')

    graph_type_inf = '; partitioning may be unsound for several calculi.'
    parser.add_argument('--graph-type', metavar='STR', nargs=1, default=False,
        required = True, type=str, choices=['complete', 'lexbfs', 'gfi'],
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

    return result.only_estimate, result.encoding[0], result.graph_type[0], \
        result.GQR_COMPOSITION_TABLE_FILE

if __name__ == '__main__':
    ONLY_ESTIMATE_SIZE, CLAUSE_TYPE, GRAPH_TYPE, CT_FILENAME = check_options()

    COMPTABLE, SIGNATURE = read_comp_table(CT_FILENAME)
    INPUT_QCN = read_gqr_csp_stdin(SIGNATURE)

    if INPUT_QCN.size == 0 or not INPUT_QCN.is_2_consistent():
        # no constraints read (assume problem was unsatisfiable) or
        # problem is not 2-consistency (=> unsat)
        print "p cnf 1 2"
        print "1 0"
        print "-1 0"
        raise SystemExit()

    # triangulation
    if GRAPH_TYPE != 'complete':
        VERTICES = set( [ X for (X, _) in INPUT_QCN.constraints.keys() ] +
                        [ X for (_, X) in INPUT_QCN.constraints.keys() ] )
        EDGES = dict( [ (V, set()) for V in VERTICES ] )
        for (I, J) in INPUT_QCN.constraints.keys():
            EDGES[I].add(J)
            EDGES[J].add(I)

        ORDER = None
        if GRAPH_TYPE == 'lexbfs':
            ORDER = lex_bfs(VERTICES, EDGES)
        else:
            assert GRAPH_TYPE == 'gfi'
            ORDER = greedy_x(VERTICES, EDGES)
        INPUT_QCN.graph = elimination_game(VERTICES, EDGES, ORDER)

    CNFINSTANCE = CNFOutput(ONLY_ESTIMATE_SIZE)
    if CLAUSE_TYPE == 'support':
        binra_support(INPUT_QCN, COMPTABLE, CNFINSTANCE)
    elif CLAUSE_TYPE == 'direct':
        binra_direct(INPUT_QCN, COMPTABLE, CNFINSTANCE)
    elif CLAUSE_TYPE == 'ord-clauses':
        import allen
        allen.ord_horn_encode_variables(INPUT_QCN, CNFINSTANCE)
    elif CLAUSE_TYPE == 'support-pa':
        import allen
        allen.pham_support_pt_encode(INPUT_QCN, CNFINSTANCE)
    elif CLAUSE_TYPE == 'direct-pa':
        import allen
        allen.pham_direct_pt_encode(INPUT_QCN, CNFINSTANCE)
    CNFINSTANCE.flush()  # note, invalidates content as well
