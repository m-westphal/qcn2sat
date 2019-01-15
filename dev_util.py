#! /usr/bin/env python
# -*- coding: UTF-8 -*-
"""Development utilities."""

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

from __future__ import absolute_import
from __future__ import print_function
import time

_SILENT = True

class TimeDelta(object):
    """Measure wall clock time deltas."""
    def __init__(self, string):
        self.name = string
        self.last_time_stamp = None
        self.set_to_current_time()

    def set_to_current_time(self):
        """Set stored time to current time."""

        self.last_time_stamp = time.time()

    def print_time_delta(self):
        """Measure and print wall clock time difference"""

        if _SILENT:
            self.set_to_current_time()
        else:
            current_time_stamp = time.time()
            delta = current_time_stamp - self.last_time_stamp
            self.last_time_stamp = current_time_stamp
            print(("[%2.2f sec] " % (delta) + self.name))
