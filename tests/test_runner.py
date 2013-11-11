#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Internal test script to run some examples."""

# ex: set tabstop=4 expandtab softtabstop=4:

# qcsp2sat.py: convert qualitative CSPs to CNF formulae
# Copyright (C) 2013  Matthias Westphal
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


TEST_INSTANCES = {
    'test_instance_1.csp':
        'd0dffeb1e15c22b1b4f694325d4058868552b5d5f824502f901e8a85a6f3b4e7',
    'test_instance_2.csp':
        'b807bd394d6a55e825623016109527c0ee4c3c67fb237383b904be4ead3490f3'
}

KNOWN_RESULTS = {
    'test_instance_1.csp': {
        '--graph-type complete --encoding support':
            'ac42a371b5a124286c410ed5dfa2e3be7ee7d5b1feac6f08e7e1715f0c3669a8',
        '--graph-type gfi --encoding support':
            'ac42a371b5a124286c410ed5dfa2e3be7ee7d5b1feac6f08e7e1715f0c3669a8',
        '--graph-type gfi --encoding direct':
            'ac42a371b5a124286c410ed5dfa2e3be7ee7d5b1feac6f08e7e1715f0c3669a8',
        '--graph-type gfi --encoding support-pa':
            'ac42a371b5a124286c410ed5dfa2e3be7ee7d5b1feac6f08e7e1715f0c3669a8',
        '--graph-type gfi --encoding direct-pa':
            'ac42a371b5a124286c410ed5dfa2e3be7ee7d5b1feac6f08e7e1715f0c3669a8',
        '--graph-type gfi --encoding ord-clauses':
            'ac42a371b5a124286c410ed5dfa2e3be7ee7d5b1feac6f08e7e1715f0c3669a8',
        '--graph-type lexbfs --encoding support':
            'ac42a371b5a124286c410ed5dfa2e3be7ee7d5b1feac6f08e7e1715f0c3669a8',
        },
    'test_instance_2.csp': {
        '--graph-type complete --encoding support':
            '541dfda42582006143353ea44c1b3fa0dd9b4440c95fc8949552f2555e1340cd',
        '--graph-type gfi --encoding support':
            'fd019ed5c640cee95085c24bfa50e1a0a8e31ba43881e7e5b05753862d281e7f',
        '--graph-type gfi --encoding direct':
            '2431277fba8aeea2cb80c8492d99c29091d712b5976529a53621f0ca42673126',
        '--graph-type gfi --encoding support-pa':
            '43ca3524a63bc2c8ba7ff6409e1e0612fea3e3b965aea9ccb897ba56cbdcd35a',
        '--graph-type gfi --encoding direct-pa':
            '564fdb44395766910a75b700bcac0416af3541c4c98decf46b0eca44ebb46290',
        '--graph-type gfi --encoding ord-clauses':
            '5a23b1a50abbdc27745f4eaaa606ea122cd142cb31e23a606d3b82ad781e7947',
        '--graph-type lexbfs --encoding support':
            'fd019ed5c640cee95085c24bfa50e1a0a8e31ba43881e7e5b05753862d281e7f',
        },
}

def get_file_location(name):
    """Wrap around waf executing script in different dir."""
    import os

    if os.path.isfile(name):
        return name

    parent_name = os.path.join('..', name)
    if os.path.isfile(parent_name):
        return parent_name

    tests_name = os.path.join('tests/', name)
    if os.path.isfile(tests_name):
        return tests_name

    waf_name = os.path.join('..', tests_name)
    if os.path.isfile(waf_name):
        return waf_name
    raise SystemExit("Could not find '%s'" % (name))

def check_instance(name, known_value):
    """Compute hash value of instance (currently SHA256)."""

    import hashlib
    value = \
    hashlib.sha256(open(name, 'rb').read()).hexdigest() # pylint: disable=E1101

    if value != known_value:
        msg = "'%s' hash value mismatch\n\tKnown\t%s\n\tActual\t%s" % (
        name, known_value, value)

        raise SystemExit(msg)
    print "Found '%s'\t'%s'" % (name, known_value)

def check_output(name, given_args, stdout, known_value):
    """Compute hash value of output (currently SHA256)."""

    import hashlib
    value = hashlib.sha256(stdout).hexdigest() # pylint: disable=E1101
    if value != known_value:
        msg = "'%s' output hash value mismatch" % name
        msg += "\n\targs\t%s\n\tKnown\t%s\n\tActual\t%s" % (given_args,
            known_value, value)
        raise SystemExit(msg)

    print "Correct '%s'\n\t'%s'\n\t\t'%s'" % (name, given_args, known_value)

def run_test(with_args, inputname):
    """Run main script with_args < input."""

    import os
    
    parent = ""

    script_name = 'qcsp2sat.py'
    if not os.path.isfile(script_name):
        script_parent = os.path.join('..', script_name)
        if os.path.isfile(script_parent):
            parent = "cd .. && "

    import subprocess

    inputfile = open(inputname, 'rb')

    allen_comp = 'data/allen.comp'
    cmdline = parent+'python '+script_name+' '+with_args+' '+allen_comp

    print "Run '%s'" % cmdline

    out = subprocess.check_output(cmdline, stdin=inputfile,
        stderr=subprocess.STDOUT, shell=True)
    inputfile.close()
    return out

if __name__ == '__main__':
    from sys import argv
    RESTRICT = False
    if len(argv) > 1:
        RESTRICT = True
    for instance in TEST_INSTANCES:
        if RESTRICT and not instance in argv:
            continue
        filename = get_file_location(instance)
        check_instance(filename, TEST_INSTANCES[instance])

        for args in KNOWN_RESULTS[instance]:
            known_output_value = KNOWN_RESULTS[instance][args]

            output = run_test(args, filename)
            check_output(instance, args, output, known_output_value)
        print "Done '%s'" % instance
