Status: Solved
== Q1: When we merge classes, should we be shrinking the size of the union find?

Simple example:
1. add variables "a", "b" (uf.size = 2)
2. unions classes with "a" and "b" (now we have 2 classes, but 1 "canonical" class)

eg.uf.size still returns 2, but the number of canonical classes is 1.

I can't think of a situation that requires us to explicitly match a "subclass of the canonical class", so there might not be a real reason to keep multiple classes going. Then we should be shrinking the union-find, but that sounds like a lot of work for minor/no benefit. 

There is also no real problem to keeping eg.uf.size = 2, as long as the IDs are canonicalised before use (which we should be doing). The eg.uf.size can be used to check the range of allowed ids.

Alternative: also implement a function that returns the number of "canonical classes"

Note: egg does not seem to shrink the uf either, running the equivalent of "testRewriteViaEquivalence" returns similar results (different canonical class id chosen, but that doesn't matter)