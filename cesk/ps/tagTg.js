var tagTg = {}

// Initial thread ID
tagTg.t0 = 0;

tagTg.thread =
  function (node, time)
  {
    // Thread IDs are just addresses
    return new ContextAddr(node.tag, null);
  }
