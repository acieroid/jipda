var unboundedHistory = {}

unboundedHistory.h0 = [];

unboundedHistory.record =
  function (context,  history)
  {
    var copy = history.slice();
    history.push(context);
    return history;
  }

