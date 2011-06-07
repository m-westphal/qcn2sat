#! /usr/bin/env python

# ex: set tabstop=4 expandtab softtabstop=4:

# qcsp2sat.py: a script to convert qualitative CSPs to CNF formulae
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



import copy, re, sys, string

class cnf:
    def __init__(self, only_estimate_size=False):
        self.only_estimate_size = only_estimate_size
        self.variables = 0
        self.clauses = []
        self.number_of_clauses = 0
        self.bytes = 0

    def add_clause(self, clause):
        self.number_of_clauses += 1
        self.variables = max( max([abs(l) for l in clause]), self.variables )
        cl = self.encode_clause(clause)
        self.bytes += len(cl)+1
        if not only_estimate_size:
            self.clauses.append(cl)

    def generate_header(self):
        assert self.variables > 0
        assert self.number_of_clauses > 0
        header = "p cnf %d %d\n" % (self.variables, self.number_of_clauses)
        return header

    def encode_clause(self, c):	# turn clause into string
        clause = [`v` for v in c] # turn into strings
        return string.join(clause+['0'])

    def write(self):
        print self.generate_header()
        for c in self.clauses:
            print c

    def get_size(self):
        return len(self.generate_header())+1+self.bytes

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

def full_qcsp(constraints, ALL_RELATIONS):  # turn the CSP into a complete constraint network
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

def writeSATdirect(constraints, calculus, only_estimate_size=False):
    comptable, ALL_RELATIONS = readCompTable(calculus)

    max_node, CSP = full_qcsp(constraints, ALL_RELATIONS)

    boolvars = { } # maps b in R_ij to boolean variable (direct encoding)

    instance = cnf(only_estimate_size)
#    print "Construct ALO, AMO clauses:",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
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
                        instance.add_clause(cl)

    if only_estimate_size:
        print "Computed %d bytes (%d MiB) of CNF formulae" % (instance.get_size(), instance.get_size()/1024**2)
    else:
        instance.write()

def writeSATgac(fd, constraints, calculus):
    print "Read qualitative composition table:",
    comptable, ALL_RELATIONS = readCompTable(calculus)
    print "done (%d base relation)" % len(ALL_RELATIONS)

    max_node, CSP = full_qcsp(constraints, ALL_RELATIONS)

    dict = { }
    cnf_bytes = 0

    print "Preparing dictionary and data structures:",
    for i in range(max_node+1):
        for j in range(i+1, max_node+1):
            for br in CSP[i*(max_node+1)+j]:
                encodeDict(i, j, br, dict)
        progress(i, max_node)
    print "done (allocated %d boolean variables for domain values)" % dict["max"]

    clauses = [ ]
    print "Construct ALO, AMO clauses:",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r = CSP[i*(max_node+1)+j]
            # ALO
            clause = gen_clause([ encodeDict(i, j, br, dict) for br in r])
            cnf_bytes += len(clause)
            clauses.append(clause)

            # AMO
            for br in r:
                for br2 in r:
                    if br < br2:
                        clause = gen_clause([ -1 * encodeDict(i, j, br, dict), -1 * encodeDict(i, j, br2, dict) ])
                        cnf_bytes += len(clause)
                        clauses.append(clause)
                    else:
                        assert br == br2 or br2 < br
        progress(i, max_node)
    print "done (%s bytes prepared)" % human_readable(cnf_bytes)

    # SUPPORT
    print "Construct GAC clauses:",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r_ij = CSP[i*(max_node+1)+j]

            for k in xrange(j+1, max_node+1): # 3 for loops iterate over constraints
                r_ik = CSP[i*(max_node+1)+k]
                r_jk = CSP[j*(max_node+1)+k]
                # r_ij, r_ik, r_jk are all sides of the triangle

                # for each falsifying triple of labels
                #    add \not triple_1, ..., \not triple_n  (BLOCKS this assignment)
                c_clauses = [ ]
                for br1 in r_ij:
                    for br2 in r_jk:
                        for br3 in r_ik:
                            if br3 in comptable[br1 + " " + br2]:
                                continue
                            cl = [ -1 * encodeDict(i, j, br1, dict), -1 * encodeDict(j, k, br2, dict), -1 * encodeDict(i, k, br3, dict) ]
                            c_clauses.append(cl)
                for c in c_clauses:
                    cl = gen_clause(c)
                    cnf_bytes += len(cl)
                    clauses.append(cl)
        progress(i, max_node)
    print "done (%s bytes prepared)" % human_readable(cnf_bytes)

    header = "p cnf %d %d\n" % ( dict["max"], len(clauses))
    cnf_bytes += len(header)
#    print "All done! Writing SAT instance (%s bytes)." % human_readable(cnf_bytes)
#    print "\t-> %d variables, %d clauses" % (dict["max"], len(clauses))
    fd.write(header)
    for c in clauses:
        fd.write(c + "\n")

if __name__ == '__main__':
    only_estimate_size = False
    model = None

    arguments = [ ]
    for a in sys.argv[1:]:
        if a[0:2] == "--":
            if a == "--only-estimate":
                only_estimate_size = True
                continue
            if a == "--direct" and model is None:
                model = 'direct'
                continue
            raise SystemExit("Unknown option '%s'" % a)
        else:
            arguments.append(a)

    if len(arguments) != 2 or model is None:
        print "qcsp2sat.py: a script to convert qualitative CSPs to CNF formulae"
        print "Copyright (C) 2009-2011  Matthias Westphal"
        print "This program comes with ABSOLUTELY NO WARRANTY."
        print "This is free software, and you are welcome to redistribute it"
        print "under certain conditions; see `GPL-3' for details."
        print
        print "Usage: qcsp2sat.py GQR_COMPOSITION_TABLE_FILE GQR_QCSP"
        print "\t--only-estimate calculate size of CNF, but do not store it"
        print "\t--direct        direct encoding"
        print
        raise SystemExit("Error in commandline arguments")

    composition_table = arguments[0]
    qcsp = readGQRCSP(arguments[1])
#    print "Loaded QCSP with", max([ t for (_, t, _) in qcsp])+1, "qualitative variables"

    if model == 'direct':
        writeSATdirect(qcsp, composition_table, only_estimate_size)
