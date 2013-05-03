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

def encodeDict(i, j, baserel, d):
    """assign a boolean variable (id number) to baserel in R_ij"""
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

def readGQRCSPstdin():
    constraints = [ ]

    lines = sys.stdin.readlines()
    for l in lines:
        res = re.search('^[ ]*([0-9]*)[ ]*([0-9]*) \((.*)\)', l)
        if res:
            x = int(res.group(1))
            y = int(res.group(2))
            assert 0 <= x < y
            rel = res.group(3).strip().split(" ")
            assert rel
            constraints.append( (x, y, rel) )

    return constraints

def completeConstraintGraph(constraints, ALL_RELATIONS):
    """turn the CSP into a complete constraint network"""
    max_node = max( [ t for (_, t, _) in constraints ] )
    CSP = dict()
    for i in xrange(0, max_node+1):
        CSP[i] = dict()
        for j in range(i+1, max_node+1):
            CSP[i][j] = ALL_RELATIONS

    for i, j, r in constraints:
        assert i < j
        assert j <= max_node
        CSP[i][j] = r

    return max_node, CSP

def directDomEncoding(instance, CSP, max_node, boolvars):
    """build (var,val) as bool variables with ALO/AMO clauses"""
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not i in CSP or not j in CSP[i]:
                continue
            r = CSP[i][j]
            # ALO
            clause = [ encodeDict(i, j, br, boolvars) for br in r ]
            instance.add_clause(clause)

            # AMO
            for br in r:
                for br2 in r:
                    if br < br2:
                        clause = [ -1 * encodeDict(i, j, br, boolvars), -1 * encodeDict(i, j, br2, boolvars) ]
                        instance.add_clause(clause)
                    else:
                        assert br == br2 or br2 < br

nogoods = [ ]
representation = dict()
def readASPSolution(filename, signature):
    global nogoods
    global representation

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
        return True

    # clear globals
    representation = dict()
    nogoods = [ ]

    return False

def intDomEncoding(instance, signature, CSP, max_node, boolvars):  # build (var,val) as bool variables with ALO/AMO clauses
    import itertools
    from os import path, listdir

    for f in listdir('data'):
        if f.endswith('.das'):
            if readASPSolution(path.join('data',f), signature):
                break
    if not representation:
        raise SystemExit('No syntactic interpretation found!')

    nr_atoms = None  # number of propositional atoms in the decomposition
    for br in signature:
        t = len(representation[br])
        if nr_atoms is None:
            nr_atoms = t
        assert t == nr_atoms

    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not i in CSP or not j in CSP[i]:  # (i,j) in CSP?
                continue
            r = CSP[i][j]

            # forbidden clauses
            for m in itertools.product([-1,1],repeat=nr_atoms):  # all models
                is_allowed = False
                for br in signature:
                    v = representation[br]
                    v.sort(key=lambda x: x[1])
                    t = tuple( [ n for (n, _) in v ] )
                    if t == m and br in r:
                        is_allowed = True
                        break
                if not is_allowed:
                    clause = [ -1 * n * encodeDict(i, j, 'atom'+str(a), boolvars) for (a,n) in enumerate(m) ]
                    instance.add_clause(clause)

def writeSATint(constraints, signature, comptable, out, cgraph):
    max_node, CSP = completeConstraintGraph(constraints, signature)

    boolvars = { } # maps propositional atoms to numbers (DIMACS format...)

    intDomEncoding(out, signature, CSP, max_node, boolvars)

#    print "Construct nogood clauses (cubic time/space):",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not (i,j) in cgraph:
                continue
            for k in xrange(j+1, max_node+1):
                for xz, xy, yz in nogoods:
                    clause = [ -1 * xy[0] * encodeDict(i, j, 'atom'+xy[1], boolvars) ]
                    clause +=[ -1 * yz[0] * encodeDict(j, k, 'atom'+yz[1], boolvars) ]
                    clause +=[ -1 * xz[0] * encodeDict(i, k, 'atom'+xz[1], boolvars) ]
                    out.add_clause(clause)

def writeSATsup(constraints, signature, comptable, out, cgraph):
    max_node, CSP = completeConstraintGraph(constraints, signature)

    boolvars = { } # maps b in R_ij to boolean variable (direct encoding)

    directDomEncoding(out, CSP, max_node, boolvars)

#    print "Construct support clauses (cubic time/space):",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not (i,j) in cgraph:
                continue
            r_ij = CSP[i][j]
            for k in xrange(j+1, max_node+1):
                if not ((i,k) in cgraph and (j,k) in cgraph):
                    continue
                r_ik = CSP[i][k]
                r_jk = CSP[j][k]
                for br1 in r_ij:
                    not_b_ij = -1 * encodeDict(i, j, br1, boolvars)
                    for br2 in r_jk:
                        intersection = frozenset(r_ik) & comptable[br1 + " " + br2]

                        cl = [ not_b_ij, -1 * encodeDict(j, k, br2, boolvars) ]
                        cl += [ encodeDict(i, k, br, boolvars) for br in intersection ]
                        out.add_clause(cl)

def writeSATdirect(constraints, signature, comptable, out, cgraph):
    max_node, CSP = completeConstraintGraph(constraints, signature)

    boolvars = { } # maps b in R_ij to boolean variable (direct encoding)

    directDomEncoding(out, CSP, max_node, boolvars)

#    print "Construct direct clauses (cubic time/space):",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not (i,j) in cgraph:
                continue
            r_ij = CSP[i][j]
            for k in xrange(j+1, max_node+1):
                if not ((i,k) in cgraph and (j,k) in cgraph):
                    continue
                r_ik = CSP[i][k]
                r_jk = CSP[j][k]
                for br1 in r_ij:
                    not_b_ij = -1 * encodeDict(i, j, br1, boolvars)
                    for br2 in r_jk:
                        intersection = frozenset(r_ik) & comptable[br1 + " " + br2]

                        cl = [ not_b_ij, -1 * encodeDict(j, k, br2, boolvars) ]
                        for br in signature:
                            if not br in intersection and br in r_ik:
                                cl2 = cl + [ -1 * encodeDict(i, k, br, boolvars) ]
                                out.add_clause(cl2)

def writeSATgac(constraints, signature, comptable, out, cgraph):
    max_node, CSP = completeConstraintGraph(constraints, signature)

    boolvars = dict()

    directDomEncoding(out, CSP, max_node, boolvars)

    # SUPPORT
#    print "Construct GAC clauses:",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            if not (i,j) in cgraph:
                continue
            r_ij = CSP[i][j]
            for k in xrange(j+1, max_node+1): # 3 for loops iterate over constraints
                if not ((i,k) in cgraph and (j,k) in cgraph):
                    continue
                r_ik = CSP[i][k]
                r_jk = CSP[j][k]
                # for each falsifying triple of labels
                #    add \not triple_1, ..., \not triple_n  (BLOCKS this assignment)
                c_clauses = [ ]
                for br1 in r_ij:
                    for br2 in r_jk:
                        supported = comptable[br1 + " " + br2] & frozenset(r_ik)
                        if not supported:
                            cl = [ -1 * encodeDict(i, j, br1, boolvars), -1 * encodeDict(j, k, br2, boolvars) ]
                            c_clauses.append(cl)
                        else:
                            not_supported = frozenset(r_ik) - supported
                            for br3 in not_supported:
                                cl = [ -1 * encodeDict(i, j, br1, boolvars), -1 * encodeDict(j, k, br2, boolvars), -1 * encodeDict(i, k, br3, boolvars) ]
                                c_clauses.append(cl)
                for cl in c_clauses:
                    out.add_clause(cl)

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
              '(2) \"gac\" does not compute prime implicates. ' \
              '(3) Syntactical processing only, chosen options may result' \
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
                   ' \"GAC via Unit Propagation\", Bacchus,' \
                   ' \"Reasoning about Temporal Relations: A Maximal' \
                   ' Tractable Subclass\", Nebel and Bürckert.' \
                   ' \"An Automatic Decomposition Method for Qualitative' \
                   ' Spatial and Temporal Reasoning\" Hué et al.'
    parser.add_argument('--encoding', metavar='STR', nargs=1, default=False,
        required=True, type=str,
        choices=['support', 'direct', 'gac', 'syn-int', 'ord-clauses',
                'support-pa', 'direct-pa'],
        help='encoding [%(choices)s]'+encoding_inf)
    parser.add_argument('GQR_COMPOSITION_TABLE_FILE')

    result = parser.parse_args()

    return result.only_estimate, result.encoding[0], result.graph_type[0], result.GQR_COMPOSITION_TABLE_FILE

if __name__ == '__main__':
    only_estimate_size, clause_type, graph_type, ct_filename = check_options()

    comptable, signature = readCompTable(ct_filename)
    qcsp = readGQRCSPstdin()

    if not qcsp:  # no constraints read; assume problem was unsatisfiable
        print "p cnf 1 2"
        print "1 0"
        print "-1 0"
        raise SystemExit()

    cgraph = None
    if graph_type == 'complete':
        vararray = range(0, max([ t for (_, t, _) in qcsp])+1)
        cgraph = frozenset([ (x,y) for x in vararray for y in vararray if x != y ])
    elif graph_type == 'lexbfs':
            vertices = set( [ t for _, t, _ in qcsp ] + [ t for t, _, _ in qcsp] )
            edges = dict( [ (v, set()) for v in vertices ] )
            for i, j, _ in qcsp:
                edges[i].add(j)
                edges[j].add(i)

            order = lexBFS(vertices, edges)
            cgraph = eliminationGame(vertices, edges, order)

    instance = cnf_output(only_estimate_size)
    if clause_type == 'support':
        writeSATsup(qcsp, signature, comptable, instance, cgraph)
    elif clause_type == 'direct':
        writeSATdirect(qcsp, signature, comptable, instance, cgraph)
    elif clause_type == 'gac':
        writeSATgac(qcsp, signature, comptable, instance, cgraph)
    elif clause_type == 'ord-clauses':
        max_node, CSP = completeConstraintGraph(qcsp, signature)
        import allen
        allen.nebel_buerckert_encode_variables(signature, instance, CSP, max_node, dict())
    elif clause_type == 'syn-int':
        writeSATint(qcsp, signature, comptable, instance, cgraph)
    elif clause_type == 'support-pa':
        max_node, CSP = completeConstraintGraph(qcsp, signature)
        import allen
        allen.pham_support_pt_encode(signature, instance, CSP, max_node, cgraph)
    elif clause_type == 'direct-pa':
        import allen
#        allen.pham_direct_pt_encode(qcsp, signature, comptable, instance, cgraph)
        raise SystemExit("Not yet implemented :(")
    instance.flush()  # note, invalidates content as well
