#! /usr/bin/env python
# encoding: utf-8

# ex: set tabstop=4 expandtab softtabstop=4:

import os

def configure(ctx):
    ctx.find_program('pylint')

def build(ctx):
    import os

    # DATA tests

    # lint verifier
    ctx(rule="pylint ${SRC}", source="tests/verify_allen_interpretation.py")
    # verify ORD-Horn map
    ctx(rule="python ../tests/${SRC[0]} ../data/${SRC[1]}",
        source='tests/verify_allen_interpretation.py data/ia_ordclauses.map syntactic_map.py')


    # collect python files
    python_code_files_main_dir = list()
    for filename in os.listdir('.'):
        if filename.endswith('.py') and os.path.isfile(filename):
            python_code_files_main_dir.append(filename)

    # lint test_runner
    ctx(rule="pylint ../tests/${SRC}", source="tests/test_runner.py")
    # run test_runner on each file separately
    for csp in os.listdir('tests/'):
        csp_source = os.path.join('tests', csp)
        if csp.endswith('.csp') and os.path.isfile(csp_source):
            ctx(rule="python ../tests/${SRC[0]} %s" % csp,
                source=['tests/test_runner.py', csp_source]+python_code_files_main_dir)

    for filename in python_code_files_main_dir:
        print filename
        ctx(rule="cd .. && pylint %s" % filename, source=filename)
