#! /usr/bin/env python
# encoding: utf-8

# ex: set tabstop=4 expandtab softtabstop=4:

import os

def configure(ctx):
    ctx.find_program('pylint')

def build(ctx):
    import os

    # test ORD-Horn map
    ctx(rule="python ../${SRC[0]} ../data/${SRC[1]}",
        source='verify_allen_interpretation.py data/ia_ordclauses.map')

    for filename in os.listdir('.'):
        if filename.endswith('.py') and os.path.isfile(filename):
            ctx(rule="pylint ${SRC}", source=filename)
