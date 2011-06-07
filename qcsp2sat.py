#! /usr/bin/env python

# ex: set tabstop=4 expandtab softtabstop=4:


import re
import sys
import string

def gen_clause(vs):
    clause = [`v` for v in vs] # turn into strings
    return string.join(clause+['0'])

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

def writeSATdirect(constraints, calculus):
    comptable, ALL_RELATIONS = readCompTable(calculus)

    max_node, CSP = full_qcsp(constraints, ALL_RELATIONS)

    boolvars = { } # maps b in R_ij to boolean variable (direct encoding)
    clauses = [ ]

#    print "Construct ALO, AMO clauses:",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r = CSP[i][j]
            # ALO
            clause = gen_clause([ encodeDict(i, j, br, boolvars) for br in r])
            clauses.append(clause)

            # AMO
            for br in r:
                for br2 in r:
                    if br < br2:
                        clause = gen_clause([ -1 * encodeDict(i, j, br, boolvars), -1 * encodeDict(i, j, br2, boolvars) ])
                        clauses.append(clause)
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
                        clause = gen_clause(cl)
                        clauses.append(clause)

    header = "p cnf %d %d\n" % ( boolvars["max"], len(clauses))
#    print "All done! Writing SAT instance (%s bytes)." % human_readable(cnf_bytes)
#    print "\t-> %d variables, %d clauses" % (dict["max"], len(clauses))
    print header
    for c in clauses:
        print c

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
    if len(sys.argv) != 3:
        raise SystemExit("Usage: <script> GQR_COMPOSITION_TABLE_FILE GQR_QCSP")

    composition_table = sys.argv[1]
    qcsp = readGQRCSP(sys.argv[2])
#    print "Loaded QCSP with", max([ t for (_, t, _) in qcsp])+1, "qualitative variables"

    writeSATdirect(qcsp, composition_table)
