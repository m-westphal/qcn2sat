#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Graph triangulation."""

# ex: set tabstop=4 expandtab softtabstop=4:

# qcn2sat.py: convert qualitative constraint networks to propositional CNF
# Copyright (C) 2009-2014  Matthias Westphal
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

def lex_bfs(vertices, edges):
    """Compute LexBFS order of vertices"""
    assert vertices
    assert edges

    order = dict()

    label = dict()
    for vertex in vertices:
        label[vertex] = [ ]
    for i in xrange(len(vertices), 0, -1):
        todo = [ vertex for vertex in vertices if not vertex in order ]
        todo.sort(key=lambda x: label[x])
        todo.reverse()
        assert label[todo[0]] >= label[todo[-1]]
        vertex = todo[0]
        order[vertex] = i
        for vertex2 in edges[vertex]:
            if not vertex2 in order:
                label[vertex2].append(i)

    return order

def greedy_x(vertices, edges):
    """The greedyX algorithm (here for GFI)"""
    assert vertices
    assert edges

    order = dict()
    import copy
    h_v = copy.deepcopy(vertices)
    h_e = copy.deepcopy(edges)

    for i in xrange(len(vertices)):
        sigma = dict()
        for vertex in h_v:
            sigma[vertex] = 0
            for nb1 in h_e[vertex]:
                for nb2 in h_e[vertex]:
                    if nb1 == nb2:
                        continue
                    assert nb1 != vertex and nb2 != vertex
                    if not nb1 in h_e[nb2]:
                        sigma[vertex] += 1
        todo = [ v for v in h_v ]
        todo.sort(key=lambda x: sigma[x])
        assert sigma[todo[0]] <= sigma[todo[-1]]
        vertex = todo[0]
        order[vertex] = i

        for nb1 in h_e[vertex]:
            for nb2 in h_e[vertex]:
                if nb1 == nb2:
                    continue
                if not nb1 in h_e[nb2]:
                    h_e[nb2].add(nb1)
                    h_e[nb1].add(nb2)

        h_v.remove(vertex)
        for ngb in h_e[vertex]:
            h_e[ngb].remove(vertex)
        del h_e[vertex]

    return order

def fill_in_build_queue(vertices, order):
    """Turn dict VERTEX->WEIGHT into a list"""

    assert vertices == set(order.keys())
    queue = list(vertices)
    queue.sort(key=lambda x: order[x]) # lowest weight first
    assert order[queue[0]] <= order[queue[1]]

    return queue

def fill_in(vertices, edges, order):
    """Compute Fill-In graph of input graph."""
    from itertools import product
    import copy

    queue = fill_in_build_queue(vertices, order)

    # add input edges
    ret = set()
    for vertex in vertices:
        for nb1 in edges[vertex]:
            ret.add( (vertex, nb1) )

    tmp_graph = copy.deepcopy(edges)
    for vertex in queue:
        # Turn vertex into a clique in tmp
        for nb1, nb2 in product(tmp_graph[vertex], tmp_graph[vertex]):
            if nb1 == nb2 or order[vertex] > order[nb1] \
                or order[vertex] > order[nb2]:

                continue

            if not nb1 in tmp_graph[nb2]:
                tmp_graph[nb1].add(nb2)
                tmp_graph[nb2].add(nb1)
                ret.add( (nb1, nb2) )
                ret.add( (nb2, nb1) )

    return frozenset(ret)

if __name__ == '__main__':
    # simple test case
    LEN = 1000
    CYCLE_V = set(range(0, LEN))
    CYCLE_E = dict([ (V, set([(V-1)%LEN, (V+1)%LEN])) for V in CYCLE_V ])
    for X in range(3, LEN, LEN/25): #  more interesting test
        CYCLE_E[X].add((X-2)%LEN)
        CYCLE_E[(X-2)%LEN].add(X)

    print "Test edges\t", len(CYCLE_E)

    import dev_util
    from dev_util import TimeDelta

    dev_util._SILENT = False

    TIME_LEXBFS = TimeDelta("LexBFS")
    ORDER_L = lex_bfs(CYCLE_V, CYCLE_E)
    TIME_LEXBFS.print_time_delta()
    print "LexBFS edges\t%d" % (len(fill_in(CYCLE_V, CYCLE_E, ORDER_L)))
    TIME_LEXBFS.print_time_delta()

    TIME_GFI = TimeDelta("GFI")
    ORDER_G = greedy_x(CYCLE_V, CYCLE_E)
    TIME_GFI.print_time_delta()
    print "GFI edges\t%d" % (len(fill_in(CYCLE_V, CYCLE_E, ORDER_G)))
    TIME_GFI.print_time_delta()
