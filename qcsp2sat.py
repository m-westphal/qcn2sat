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

__VERSION="0.1 alpha"

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
        self.bytes = 0

    def add_clause(self, clause):
        self.number_of_clauses += 1
        self.variables = max( max([abs(l) for l in clause]), self.variables )
        cl = self.encode_clause(clause)
        self.bytes += len(cl)
        if not only_estimate_size:
            chunk = self.bzip2.compress(cl)
            if chunk:
                self.clauses_bz2.append(chunk)

    def generate_header(self):
        assert self.variables > 0
        assert self.number_of_clauses > 0
        header = "p cnf %d %d" % (self.variables, self.number_of_clauses)
        return header

    def encode_clause(self, c): # turn clause into string
        clause = [`v` for v in c] # turn into strings
        return string.join(clause+['0\n'])

    def flush(self):    # invalidates class content
        if self.only_estimate_size:
            print "Constructed %d variables and %d clauses" % (self.get_nr_variables(), self.get_nr_clauses())
            print "Computed %d bytes (%d MiB) of CNF formulae" % (self.get_size(), self.get_size()/1024**2)
        else:
            self.clauses_bz2.append(self.bzip2.flush())
            del self.bzip2

            self.fd.write(self.generate_header()+'\n')
            decomp = bz2.BZ2Decompressor()
            while self.clauses_bz2:
                chunk = self.clauses_bz2.popleft()
                self.fd.write(decomp.decompress(chunk))
            del decomp

    def get_size(self):
        return len(self.generate_header())+1+self.bytes

    def get_nr_variables(self):
        return self.variables

    def get_nr_clauses(self):
        return self.number_of_clauses

def readGQRCSP(csp):
    constraints = [ ]

    lines = open(csp, 'r')
    for l in lines:
        res = re.search('^[ ]*([0-9]*)[ ]*([0-9]*) \((.*)\)', l)
        if res:
            x = int(res.group(1))
            y = int(res.group(2))
            assert 0 <= x < y
            rel = res.group(3).strip().split(" ")
            assert rel
            constraints.append( (x, y, rel) )
    lines.close()

    return constraints

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

def completeConstraintGraph(constraints, ALL_RELATIONS):  # turn the CSP into a complete constraint network
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

def directDomEncoding(instance, CSP, max_node, boolvars):  # build (var,val) as bool variables with ALO/AMO clauses
    #    print "Construct ALO, AMO clauses:",
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

def writeSATdirect(constraints, signature, comptable, out):
    max_node, CSP = completeConstraintGraph(constraints, signature)

    boolvars = { } # maps b in R_ij to boolean variable (direct encoding)

    directDomEncoding(out, CSP, max_node, boolvars)

#    print "Construct support clauses (cubic time/space):",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r_ij = CSP[i][j]
            for k in xrange(j+1, max_node+1):
                r_ik = CSP[i][k]
                r_jk = CSP[j][k]
                for br1 in r_ij:
                    not_b_ij = -1 * encodeDict(i, j, br1, boolvars)
                    for br2 in r_jk:
                        intersection = frozenset(r_ik) & comptable[br1 + " " + br2]

                        cl = [ not_b_ij, -1 * encodeDict(j, k, br2, boolvars) ]
                        cl += [ encodeDict(i, k, br, boolvars) for br in intersection ]
                        out.add_clause(cl)

def writeSATgac(constraints, signature, comptable, out):
    max_node, CSP = completeConstraintGraph(constraints, signature)

    boolvars = dict()

    directDomEncoding(out, CSP, max_node, boolvars)

    # SUPPORT
#    print "Construct GAC clauses:",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r_ij = CSP[i][j]

            for k in xrange(j+1, max_node+1): # 3 for loops iterate over constraints
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

    queue = [ vertices.copy() ]
    order = [ ]

    while queue:
        if not queue[0]:
            del queue[0]
            continue
        v = queue[0].pop()
        if not queue[0]:
            del queue[0]

        order.append(v)

        replaced = dict()
        for y in edges[v]:
            for q in queue:
                if y in q:
                    rep = set()
                    if not v in replaced:
                        replaced[v] = rep
                        queue.insert(queue.index(q), rep)
                    else:
                        rep = replaced[v]
                    q.remove(y)
                    rep.add(y)

    return dict( [ (v, order.index(v)) for v in order ] )

def eliminationGame(vertices, edges, order):
    import copy

    new_edges = [ edges.copy() ]

    queue = list(vertices)
    queue.sort(lambda a,b: order[b] - order[a]) # highest weight first

    while queue:
        v = queue[0]
        del queue[0]

        tmp = copy.deepcopy(new_edges[-1])

        for x in tmp[v]:
            assert v in tmp[x]
            for y in tmp[v]:
                if x != y:
                    tmp[x].add(y)
        for z in tmp[v]:
            tmp[z].remove(v)
        del tmp[v]
        new_edges.append(tmp)

    del new_edges[-1]

    final = dict( [ (v, set()) for v in vertices ] )
    for graph in new_edges:
        for v in graph:
            for n in graph[v]:
                final[v].add(n)

    ret = set()
    for v1 in vertices:
        ret |= set( [ (v1, v2) for v2 in final[v1] ] )
    return frozenset(ret)

def writeSATpartition(constraints, signature, comptable, out):
    max_node = max( [ t for _, t, _ in constraints] )
    CSP = dict()
    for i, j, r in constraints:
        if not i in CSP:
            CSP[i] = dict()
        CSP[i][j] = r
        assert frozenset(r) != signature

    boolvars = dict()

    directDomEncoding(out, CSP, max_node, boolvars)

    # constraint graph for triangulation
    vertices = set( [ t for _, t, _ in constraints ] + [ t for t, _, _ in constraints] )
    edges = dict( [ (v, set()) for v in vertices ] )
    for i in CSP:
        for j in CSP[i]:
            edges[i].add(j)
            edges[j].add(i)

    order = lexBFS(vertices, edges)
    chordal_graph = eliminationGame(vertices, edges, order)
    fullcsp = completeConstraintGraph(constraints, signature)[1]
#    print "Construct support clauses restricted to chordal graph (cubic time/space):",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r_ij = fullcsp[i][j]
            if not (i,j) in chordal_graph:
                assert frozenset(r_ij) == signature
                continue
            for k in xrange(j+1, max_node+1):
                if not ((j,k) in chordal_graph and (i,k) in chordal_graph):
                    continue
                r_ik = fullcsp[i][k]
                r_jk = fullcsp[j][k]
                for br1 in r_ij:
                    not_b_ij = -1 * encodeDict(i, j, br1, boolvars)
                    for br2 in r_jk:
                        intersection = frozenset(r_ik) & comptable[br1 + " " + br2]

                        cl = [ not_b_ij, -1 * encodeDict(j, k, br2, boolvars) ]
                        cl += [ encodeDict(i, k, br, boolvars) for br in intersection ]
                        out.add_clause(cl)

if __name__ == '__main__':
    only_estimate_size = False
    model = None

    arguments = [ ]
    for a in sys.argv[1:]:
        if a[0:2] == "--":
            if a == "--only-estimate":
                only_estimate_size = True
                continue
            M = [ "direct-sup", "direct-gac", "direct-part-sup" ]
            for m in M:
                if a[2:] == m:
                    if model is None:
                        model = m
                    else:
                        model = "invalid"
                    break
            else:
                raise SystemExit("Unknown option '%s'" % a)
        else:
            arguments.append(a)

    if len(arguments) != 2 or model is None or model == "invalid":
        print "qcsp2sat.py: convert qualitative CSPs to CNF formulae (version %s)" % __VERSION
        print "Copyright (C) 2009-2011  Matthias Westphal"
        print "This program comes with ABSOLUTELY NO WARRANTY."
        print "This is free software, and you are welcome to redistribute it"
        print "under certain conditions; see `GPL-3' for details."
        print
        print "Usage: qcsp2sat.py GQR_COMPOSITION_TABLE_FILE GQR_QCSP"
        print "    --only-estimate      calculate size of CNF, but do not store clauses"
        print "    --direct-sup         direct encoding with simple support clauses"
        print "                         (see \"SAT 1-D support encoding\" in \"Towards"
        print "                         An Efficient SAT Encoding for Temporal"
        print "                         Reasoning\", Pham et al.)"
        print "    --direct-gac         direct encoding with clauses that establish GAC"
        print "                         (see \"GAC via Unit Propagation\", Bacchus;"
        print "                         NOTE: the script does not compute prime"
        print "                         implicates!)"
        print "    --direct-part-sup    direct encoding restricted to tree decomposition"
        print "                         (see ?) [EXPERIMENTAL!] (potentially unsound for"
        print "                         several calculi)"
        print
        print "WARNING: the script is completely untested and potentially unsound!"
        print
        raise SystemExit("Error in commandline arguments")

    comptable, signature = readCompTable(arguments[0])
#    print "Loaded calculus with", len(signature), "qualitative binary relations"
    qcsp = readGQRCSP(arguments[1])
#    print "Loaded QCSP with", max([ t for (_, t, _) in qcsp])+1, "qualitative variables"


    instance = cnf_output(only_estimate_size)
    if model == 'direct-sup':
        writeSATdirect(qcsp, signature, comptable, instance)
    if model == 'direct-gac':
        writeSATgac(qcsp, signature, comptable, instance)
    if model == 'direct-part-sup':
        writeSATpartition(qcsp, signature, comptable, instance)
    instance.flush() # note, invalidates content as well
