#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Development utilities."""

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

LAST_TIME_STAMP = None
def print_time_delta(val):
    """Measure and print wall clock time difference"""
    global LAST_TIME_STAMP   # pylint: disable=W0603
    import time

    if type(val) == bool:
        if val:
            assert LAST_TIME_STAMP is None
            LAST_TIME_STAMP = time.time()
    elif not LAST_TIME_STAMP is None:
        current_time_stamp = time.time()
        delta = current_time_stamp - LAST_TIME_STAMP
        print("[%2.2f sec] " % (delta) + val)
        LAST_TIME_STAMP = current_time_stamp
