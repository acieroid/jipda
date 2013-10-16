var tagTg = {}

tagTg.thread =
  function (node)
  {
    // Thread IDs are just addresses
    return new ContextAddr(node.tag, null);
  }
