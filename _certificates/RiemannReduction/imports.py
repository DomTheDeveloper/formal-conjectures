"""Conservative reachability queries on the source import graph."""
from functools import lru_cache
from graphlib import TopologicalSorter

class Imports:
    def __init__(self, imports):
        self.graph = imports
        self.order = list(TopologicalSorter(imports).static_order())
        self.position = {name:i for i,name in enumerate(self.order)}
        self.mathlib = {}
        self.descendants = {}
        # A small necessary reachability signature makes negative queries cheap.
        for name in self.order:
            deps = imports.get(name, ())
            self.mathlib[name] = name == 'Mathlib' or any(self.mathlib[d] for d in deps)
            bits = 1 << ((self.position[name] * 2654435761 >> 19) % 256)
            for dep in deps:
                bits |= self.descendants[dep]
            self.descendants[name] = bits

    @lru_cache(maxsize=150000)
    def reaches(self, source, target):
        if source == target:
            return True
        if self.position[source] <= self.position[target]:
            return False
        wanted = self.descendants[target]
        floor = self.position[target]
        pending, seen = [source], set()
        while pending and len(seen) < 256:
            here = pending.pop()
            if here in seen or self.position[here] <= floor or wanted & ~self.descendants[here]:
                continue
            seen.add(here)
            for dep in self.graph.get(here, ()):
                if dep == target:
                    return True
                pending.append(dep)
        # An inconclusive bounded search leaves the source untouched.
        return False

    def redundant(self, names):
        kept = []
        result = []
        for i, name in enumerate(names):
            if any(self.reaches(prior, name) for prior in reversed(kept)):
                result.append(i)
            else:
                kept.append(name)
        return result
