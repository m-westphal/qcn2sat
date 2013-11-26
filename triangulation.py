#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Graph triangulation."""

# ex: set tabstop=4 expandtab softtabstop=4:

# qcn2sat.py: convert qualitative constraint networks to propositional CNF
# Copyright (C) 2009-2013  Matthias Westphal
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

def elimination_game_build_queue(vertices, order):
    """Turn dict VERTEX->WEIGHT into a list"""

    assert vertices == set(order.keys())
    queue = list(vertices)
    queue.sort(key=lambda x: order[x]) # lowest weight first
    assert order[queue[0]] <= order[queue[1]]

    return queue

def elimination_game(vertices, edges, order):
    """Run the elimination game"""
    from itertools import product
    import copy

    new_edges = [ edges.copy() ] # G^0

    queue = elimination_game_build_queue(vertices, order)

    for vertex in queue:
        tmp = copy.deepcopy(new_edges[-1]) # G^{i-1}

        # Turn v into a clique in tmp
        for nb1, nb2 in product(new_edges[-1][vertex], new_edges[-1][vertex]):
            if nb1 == nb2:
                continue
            tmp[nb1].add(nb2)
            tmp[nb2].add(nb1)
        # remove v from G^i
        for nb1 in tmp:
            tmp[nb1].discard(vertex) # remove edges to vertex if present
        del tmp[vertex] # remove vertex itself
        new_edges.append(tmp) # add G^i

    final = dict( [ (vertex, set()) for vertex in vertices ] )
    for graph in new_edges[:-1]:
        for vertex in graph:
            final[vertex] |= graph[vertex]

    ret = set()
    for vertex in vertices:
        ret |= set( [ (vertex, x) for x in final[vertex] ] )
    return frozenset(ret)

if __name__ == '__main__':
    # simple test case
    LEN = 500
    CYCLE_V = set(range(0, LEN))
    CYCLE_E = dict([ (V, set([(V-1)%LEN, (V+1)%LEN])) for V in CYCLE_V ])
    for X in range(3, LEN, LEN/25): #  more interesting test
        CYCLE_E[X].add((X-2)%LEN)
        CYCLE_E[(X-2)%LEN].add(X)

    import dev_util

    dev_util.print_time_delta(True)
    ORDER_L = lex_bfs(CYCLE_V, CYCLE_E)
    dev_util.print_time_delta("Order: Lex BFS")
    ORDER_G = greedy_x(CYCLE_V, CYCLE_E)
    dev_util.print_time_delta("Order: GFI")

    print "Test edges\t", len(CYCLE_E)
    print "LexBFS edges\t", len(elimination_game(CYCLE_V, CYCLE_E, ORDER_L))
    dev_util.print_time_delta("Elimination game (Lex BFS)")
    print "GFI edges\t", len(elimination_game(CYCLE_V, CYCLE_E, ORDER_G))
    dev_util.print_time_delta("Elimination game (GFI)")
