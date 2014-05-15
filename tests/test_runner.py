#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Internal test script to run some examples."""

# ex: set tabstop=4 expandtab softtabstop=4:

# qcn2sat.py: convert qualitative constraint networks to propositional CNF
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
        'b807bd394d6a55e825623016109527c0ee4c3c67fb237383b904be4ead3490f3',
    'test_instance_3.csp':
        '103bc467a875ac12cb1a77b730c707b04c5f3ff20634e7919fa3ae27de08ba3f',
    'test_instance_rcc8.csp':
        '6488b05a3e1aee9d02db4362a525ce035375b95ac4514021df7ed5c0a0d8c489',
}

CALCULUS = {
    'test_instance_1.csp': 'allen',
    'test_instance_2.csp': 'allen',
    'test_instance_3.csp': 'allen',
    'test_instance_rcc8.csp': 'rcc8',
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
            'a66f58898591f28862eb3dfb1f98fa64b2e997e639eb2673b76f52d7870e4cd5',
        '--graph-type gfi --encoding support-pa':
            '43ca3524a63bc2c8ba7ff6409e1e0612fea3e3b965aea9ccb897ba56cbdcd35a',
        '--graph-type gfi --encoding direct-pa':
            '564fdb44395766910a75b700bcac0416af3541c4c98decf46b0eca44ebb46290',
        '--graph-type gfi --encoding ord-clauses':
            '5a23b1a50abbdc27745f4eaaa606ea122cd142cb31e23a606d3b82ad781e7947',
        '--graph-type lexbfs --encoding support':
            'fd019ed5c640cee95085c24bfa50e1a0a8e31ba43881e7e5b05753862d281e7f',
        },
    'test_instance_3.csp': {
        '--graph-type complete --encoding support':
            'c0f484380994eb6521f09173e9b8adc6788b99e716c2221d2e59724aa1c6718a',
        '--graph-type complete --encoding ord-clauses':
            '107baf68764551af8e2b2f47dbc57343b8c2708441bdb09b986a1a62feb0a34e',
        '--graph-type gfi --encoding support':
            '969a0896fff5f4cc63eeca50cae2d810222ecc3aab5ea01dde53a6e67295e249',
        '--graph-type gfi --encoding direct':
            '8b2bd678bdf98a75f5d95cee1aa33f9177c4e83169d7e1ce53cc57e65daebb80',
        '--graph-type gfi --encoding support-pa':
            '9bc50bcd98be85022ffc12870efed2715e67aaf736f67149649dd5a451fc7d17',
        '--graph-type gfi --encoding direct-pa':
            'b1fdce62fe212ba4aab95818d66b2cfd8d3b6e62efdc7e1855a06952e0999cd6',
        '--graph-type gfi --encoding ord-clauses':
            '61d720ea01f0adc251675be047663fbf73ef8d3910f54a2967b6857d859005cf',
        '--graph-type lexbfs --encoding support':
            '969a0896fff5f4cc63eeca50cae2d810222ecc3aab5ea01dde53a6e67295e249',
        '--graph-type lexbfs --encoding ord-clauses':
            '61d720ea01f0adc251675be047663fbf73ef8d3910f54a2967b6857d859005cf',
        },
    'test_instance_rcc8.csp': {
        '--graph-type gfi --encoding rcc8-rcc4':
            'd4218cd079c6e6b56aa63b7e2f07039a1c54cef06c9c2a49c95265184248b785',
        '--graph-type gfi --encoding support':
            '9208e01f98e2952b9e6ba4b5aa72ca566afd483ca273710f4cbc05cd8b83b915',
        '--graph-type gfi --encoding direct':
            '4ffec259f9d0fa01b69ec62545cee97c756c6fff0930a84b68bba258b1ab1030',
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
        msg = "FAIL '%s' hash value mismatch\n\tKnown\t%s\n\tActual\t%s" % (
        name, known_value, value)

        raise SystemExit(msg)
    print "Found '%s'\t'%s'" % (name, known_value)

def check_output(name, given_args, stdout, known_value):
    """Compute hash value of output (currently SHA256)."""

    import hashlib
    value = hashlib.sha256(stdout).hexdigest() # pylint: disable=E1101
    if value != known_value:
        msg = "FAIL '%s' output hash value mismatch" % name
        msg += "\n\targs\t%s\n\tKnown\t%s\n\tActual\t%s" % (given_args,
            known_value, value)
        raise SystemExit(msg)

    print "Correct '%s'\n\t'%s'\n\t\t'%s'" % (name, given_args, known_value)

def run_test(with_args, calculus, inputname):
    """Run main script with_args < input."""

    import os
    
    parent = ""

    script_name = 'qcn2sat.py'
    if not os.path.isfile(script_name):
        script_parent = os.path.join('..', script_name)
        if os.path.isfile(script_parent):
            parent = "cd .. && "

    import subprocess

    inputfile = open(inputname, 'rb')

    comp = 'data/%s.comp' % calculus
    cmdline = parent+'python '+script_name+' '+with_args+' '+comp

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

            output = run_test(args, CALCULUS[instance], filename)
            check_output(instance, args, output, known_output_value)
        print "Done '%s'" % instance
