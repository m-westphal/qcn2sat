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
        if self.only_estimate_size:
            self.bytes = 0

    def add_clause(self, clause):
        self.number_of_clauses += 1
        self.variables = max( max([abs(l) for l in clause]), self.variables )
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

    def encode_clause(self, c): # turn clause into string
        clause = [`v` for v in c] # turn into strings
        return string.join(clause+['0\n'])

    def flush(self):    # invalidates class content
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

    for f in [ 'rcc5.solution', 'rcc8.solution']:
        if readASPSolution(f, signature):
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

def parse_cmdline(argv):
    only_estimate_size = False
    arguments = [ ]
    graph_type = None
    clause_type = None
    for a in argv:
        if a[0:2] == "--":
            if a == "--only-estimate":
                only_estimate_size = True
                continue
            C = [ "support", "gac", "syntactic-int" ]
            G = [ "complete", "partition-lexbfs" ]
            for m in C:
                if a[2:] == m:
                    if clause_type is None:
                        clause_type = m
                    else:
                        raise SystemExit("Two conflicting clause encodings selected")
                    break
            else:
                for m in G:
                    if a[2:] == m:
                        if graph_type is None:
                            graph_type = m
                        else:
                            raise SystemExit("Two conflicting graph encodings selected")
                        break
                else:
                    raise SystemExit("Unknown option '%s'" % a)
        else:
            arguments.append(a)

    return only_estimate_size, clause_type, graph_type, arguments

def check_options(arguments, clause_type, graph_type):
    if len(arguments) != 2 or clause_type is None or graph_type is None:
        print "qcsp2sat.py: convert qualitative CSPs to CNF formulae (version %s)" % __VERSION
        print "Copyright (C) 2009-2011  Matthias Westphal"
        print "This program comes with ABSOLUTELY NO WARRANTY."
        print "This is free software, and you are welcome to redistribute it"
        print "under certain conditions; see `GPL-3' for details."
        print
        print "Usage: qcsp2sat.py OPTIONS GQR_COMPOSITION_TABLE_FILE GQR_QCSP"
        print "    --only-estimate      calculate size of CNF, but do not store clauses"
        print "    --complete           write complete constrain graph on vars 1 .. n"
        print "    --partition-lexbfs   triangulate graph with lexbfs ordering"
        print "                         (see ?) [EXPERIMENTAL!] (potentially unsound for"
        print "                         several calculi)"
        print "    --support            direct encoding with simple support clauses"
        print "                         (see \"SAT 1-D support encoding\" in \"Towards"
        print "                         An Efficient SAT Encoding for Temporal"
        print "                         Reasoning\", Pham et al.)"
        print "    --gac                direct encoding with clauses that establish GAC"
        print "                         (see \"GAC via Unit Propagation\", Bacchus;"
        print "                         NOTE: the script does not compute prime"
        print "                         implicates!)"
        print "    --syntactic-int      syntactic interpretation of relations [WIP]"
        print
        print "WARNING: the script is completely untested and potentially unsound!"
        print
        raise SystemExit("Error in commandline arguments")
    if clause_type == "syntactic-int" and graph_type != "complete":
        raise SystemExit("Error: --syntactic-int requires --complete!")

if __name__ == '__main__':
    only_estimate_size, clause_type, graph_type, arguments = parse_cmdline(sys.argv[1:])
    check_options(arguments, clause_type, graph_type)

    comptable, signature = readCompTable(arguments[0])
#    print "Loaded calculus with", len(signature), "qualitative binary relations"
    qcsp = readGQRCSP(arguments[1])
#    print "Loaded QCSP with", max([ t for (_, t, _) in qcsp])+1, "qualitative variables"

    cgraph = None
    if graph_type == 'complete':
        vararray = range(0, max([ t for (_, t, _) in qcsp])+1)
        cgraph = frozenset([ (x,y) for x in vararray for y in vararray ])
    elif graph_type == 'partition-lexbfs':
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
    if clause_type == 'gac':
        writeSATgac(qcsp, signature, comptable, instance, cgraph)
    if clause_type == 'syntactic-int':
        writeSATint(qcsp, signature, comptable, instance, cgraph)
    instance.flush() # note, invalidates content as well
