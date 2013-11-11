#! /usr/bin/env python
# encoding: utf-8

# ex: set tabstop=4 expandtab softtabstop=4:

import os

def configure(ctx):
    ctx.find_program('pylint')

def build(ctx):
    import os

    # DATA tests
    ctx(rule="pylint ../tests/${SRC}", source="tests/verify_allen_interpretation.py")

    # test ORD-Horn map
    ctx(rule="python ../tests/${SRC[0]} ../data/${SRC[1]}",
        source='tests/verify_allen_interpretation.py data/ia_ordclauses.map syntactic_map.py')

    for filename in os.listdir('.'):
        if filename.endswith('.py') and os.path.isfile(filename):
#            ctx(rule="pylint ${SRC}", source=filename)
            pass
