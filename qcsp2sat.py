#! /usr/bin/env python

# ex: set tabstop=4 expandtab softtabstop=4:


import re
import sys
import string

def human_readable(i):
    if i > 1024**3:
        return str(i/(1024**3))+"Gi"
    if i > 1024**2:
        return str(i/(1024**2))+"Mi"
    if i > 1024*2:
        return str(i/1024)+"Ki"
    return str(i)

def progress(idx, total):
    if idx == 0:
        sys.stdout.flush()

    if idx+1 == total:
        print ".",
        sys.stdout.flush()
        return

    total_f = float(total)
    for f in [0.25,0.5,0.75]:
        if idx == int(f * total_f):
            print ".",
            sys.stdout.flush()
            return

def gen_clause(vs):
    clause = [`v` for v in vs] # turn into strings
    return string.join(clause+['0\n'])

def readGQRCSP(csp):
    constraints = [ ]

    lines = open(csp, 'r')
    for l in lines:
        res = re.search('^[ ]*([0-9]*)[ ]*([0-9]*) \((.*)\)', l)
        if res:
            x = int(res.group(1))
            y = int(res.group(2))
            assert x < y
            rel = res.group(3).strip().split(" ")
            assert rel
            constraints.append((x,y,rel))

    lines.close()
    return constraints

def encodeDict(i, j, baserel, dict):
    br = string.join([str(i),str(j), baserel])
    try:
        return dict[br]
    except KeyError:
        assert i < j
        try:
            dict["max"] += 1
        except KeyError:
            dict["max"] = 1

        ret = dict["max"]
        dict[br] = ret
        return ret

def readCompTable(calculus):
    table = { }
    ALL_RELATIONS = [ ]

    lines = open(calculus, 'r')
    for l in lines:
        extract = re.search('^(.*):(.*)::.*\((.*)\)$', l)
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

def full_qcsp(constraints, ALL_RELATIONS):
    max_node = max( [ t for (_, t, _) in constraints ] )
    CSP = dict()

    defined_pairs = [ ] # used (explicit) constraint scopes
    for i, j, r in constraints:
        assert i < j
        assert j <= max_node

        CSP[i*(max_node+1)+j] = r

    for i in range(max_node+1):
        for j in range(i+1, max_node+1):
            key = i*(max_node+1)+j
            if key not in CSP.keys():
                CSP[key] = ALL_RELATIONS

    return max_node, CSP

def writeSATdirect(fd, constraints, calculus):
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
    print "done (allocated %d boolean variables)" % dict["max"]

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
    print "Construct support clauses (cubic time/space):",
    for i in xrange(max_node+1):
        for j in xrange(i+1, max_node+1):
            r_ij = CSP[i*(max_node+1)+j]

            for k in xrange(j+1, max_node+1):
                r_ik = CSP[i*(max_node+1)+k]
                r_jk = CSP[j*(max_node+1)+k]
                for br1 in r_ij:
                    not_b_ij = -1 * encodeDict(i, j, br1, dict)
                    for br2 in r_jk:
                        intersection = frozenset(r_ik) & comptable[br1 + " " + br2]

                        cl = [ not_b_ij, -1 * encodeDict(j, k, br2, dict) ]
                        cl += [ encodeDict(i, k, br, dict) for br in intersection ]
                        clause = gen_clause(cl)
                        cnf_bytes += len(clause)
                        clauses.append(clause)
        progress(i, max_node)
    print "done (%s bytes prepared)" % human_readable(cnf_bytes)

    header = "p cnf %d %d\n" % ( dict["max"], len(clauses))
    cnf_bytes += len(header)
    print "All done! Writing SAT instance (%s bytes)." % human_readable(cnf_bytes)
    print "\t-> %d variables, %d clauses" % (dict["max"], len(clauses))
    fd.write(header)
    for c in clauses:
        fd.write(c + "\n")

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
    print "All done! Writing SAT instance (%s bytes)." % human_readable(cnf_bytes)
    print "\t-> %d variables, %d clauses" % (dict["max"], len(clauses))
    fd.write(header)
    for c in clauses:
        fd.write(c + "\n")

if __name__ == '__main__':
    if len(sys.argv) != 4:
        raise SystemExit("Usage: <script> GQR_COMPOSITION_TABLE_FILE GQR_QCSP OUTPUTFILE")

    qcsp = readGQRCSP(sys.argv[2])
    print "Loaded QCSP with", max([ t for (_, t, _) in qcsp])+1, "qualitative variables"

    outfile = open(sys.argv[3], 'w')
    writeSATdirect(outfile, qcsp, sys.argv[1])
