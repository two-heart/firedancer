import cpp
predicate included(Location loc) {
  loc.getFile().getRelativePath().prefix(5) != "agave/"
}