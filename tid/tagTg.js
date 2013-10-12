var tagTg = {}

tagTg.thread =
  function (node, time)
  {
    // Thread IDs are just addresses
    return new ContextAddr(node.tag, null);
  }
