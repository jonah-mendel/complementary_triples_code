// Exact complementary-triples computations used by the IJAC paper.
// Run Magma from this directory and type:  load "load.m";

if not FileExists("data/smalltypenumber.m") then
    error "Missing data/smalltypenumber.m. Download smalltypenumber.m from https://www.math.uni-bielefeld.de/~mkirschm/orders/ and place it in data/.";
end if;

load "data/smalltypenumber.m";
load "src/orders.m";
load "src/quotients.m";
load "src/classification.m";
load "src/obstructions.m";
load "src/presentations.m";
