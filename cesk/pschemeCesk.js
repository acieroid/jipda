function pschemeCesk(cc)
{
  // address generator
  var a = cc.a;
  // TID generator
  var t = cc.t;
  // Thread history builder
  var h = cc.h;
  // benv creator
  // var b = cc.b || new DefaultBenv();
  // primitive lattice
  var p = cc.p;

  var memo = cc.memo || false;

  assertDefinedNotNull(a);
  assertDefinedNotNull(t);
  // assertDefinedNotNull(b);
  assertDefinedNotNull(p);

  // lattice (primitives + addresses)
  var l = new JipdaLattice(p); // TODO this will become param

  // install constants
  var L_UNDEFINED = l.abst1(undefined);
  var L_NULL = l.abst1(null);
  var L_0 = l.abst1(0);
  var L_1 = l.abst1(1);
  var L_TRUE = l.abst1(true);
  var L_FALSE = l.abst1(false);
  var P_0 = p.abst1(0);
  var P_1 = p.abst1(1);
  var P_TRUE = p.abst1(true);
  var P_FALSE = p.abst1(false);
  var P_NUMBER = p.NUMBER;
  var P_STRING = p.STRING;
  var P_DEFINED = P_TRUE.join(P_FALSE).join(P_NUMBER).join(P_STRING);

  // Σ = Threads × Store
  function MachineState(threads, store)
  {
    this.threads = threads;
    this.store = store;
  }
  MachineState.prototype.equals =
    function (x)
    {
      if ((x instanceof MachineState)
          && Eq.equals(this.store, x.store)
          && this.threads.length === x.threads.length)
      {
        for (var i = 0; i < this.threads.length; i++)
        {
          if (!Eq.equals(this.threads.get(i, null), x.threads.get(i, null)))
          {
            return false;
          }
        }
        return true;
      }
      return false;
    }
  MachineState.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      for (var i = 0; i < this.threads.length; i++)
      {
        result = prime * result + this.threads.get(i, null).hashCode();
      }
      return result;
    }
  MachineState.prototype.setStore =
    function (store)
    {
      return new MachineState(this.threads, store);
    }
  MachineState.prototype.getBenva =
    function (tid)
    {
      var thread = this.threads.get(tid, null);
      // assert(thread != null);
      return thread.context.benva;
    }
  MachineState.prototype.setBenva =
    function (tid, benva)
    {
      var thread = this.threads.get(tid, null);
      // assert(thread != null);
      thread = thread.setBenva(benva);
      return new MachineState(threads.put(tid, thread), this.store);
    }
  MachineState.prototype.getNode =
    function (tid)
    {
      var thread = this.threads.get(tid, null);
      // assert(thread !== null);
      return thread.context.node;
    }
  MachineState.prototype.setNode =
    function (tid, node)
    {
      var thread = this.threads.get(tid, null);
      // assert(thread !== null);
      thread = thread.setNode(node);
      return new MachineState(threads.put(tid, thread), this.store);
    }

  // Context = Exp × Env × Addr × Hist
  // where Addr is the address of the continuation
  function Context(node, benva, frame, history)
  {
    this.node = node;
    this.benva = benva;
    this.frame = frame;
    this.history = history;
  }
  Context.prototype.toString =
    function ()
    {
      return "Context(" + this.node.tag + ", " + this.benva + ")";
    }
  Context.prototype.equals =
    function (x)
    {
      return (x instanceof Context)
        && this.node === x.node
        && Eq.equals(this.benva, x.benva)
        && Eq.equals(this.frame, x.frame)
        && Eq.equals(this.history, x.history);
    }
  Context.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.benva.hashCode();
      result = prime * result + this.frame.hashCode();
      result = prime * result + this.history.hashCode();
    }
  Context.prototype.setNode =
    function (node)
    {
      return new Context(node, this.benva, this.frame, this.history);
    }
  Context.prototype.setBenva =
    function (benva)
    {
      return new Context(this.node, benva, this.frame, this.history);
    }

  // Threads = TID × Context
  function Thread(tid, context)
  {
    this.tid = tid;
    this.context = context;
  }
  Thread.prototype.toString =
    function ()
    {
      return "Thread(" + this.tid + " " + this.context + ")";
    }
  Thread.prototype.equals =
    function (x)
    {
      return (x instanceof Thread)
        && this.tid === x.tid
        && Eq.equals(this.context, x.context);
    }
  Thread.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.tid;
      result = prime * result + this.context.hashCode();
    }
  Thread.prototype.addresses =
    function ()
    {
      return [this.context.benva];
    }
  Thread.prototype.setNode =
    function (node)
    {
      return new Thread(this.tid, this.context.setNode(node));
    }
  Thread.prototype.setBenva =
    function (benva)
    {
      return new Thread(this.tid, this.context.setBenva(benva));
    }

  function Closure(node, statica, params, body)
  {
    this.node = node;
    this.statica = statica;
    this.params = params;
    this.body = body;
  }
  Closure.prototype.toString =
    function ()
    {
      return "(" + this.node.tag + " " + this.statica + ")";
    }
  Closure.prototype.nice =
    function ()
    {
      return "<Closure " + this.node.tag + ">"
    }
  Closure.prototype.equals =
    function (other)
    {
      if (this === other)
      {
        return true;
      }
      if (!(this instanceof Closure))
      {
        return false;
      }
      return this.node === other.node
        && this.statica.equals(other.statica);
    }
  Closure.prototype.hashCode =
    function (x)
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.statica.hashCode();
      return result;
    }
  Closure.prototype.apply_ =
    function (application, operandValues, tid, state, kont)
    {
      var store = state.store;
      var benva = state.getBenva(tid);
      var fun = this.node;
      var statica = this.statica;
      var extendedBenva = a.benv(application, benva, store, kont);
      var extendedBenv = Benv.empty(statica);
      var params = this.params;
      var i = 0;
      while (!(params instanceof Null))
      {
        var param = params.car;
        extendedBenv = extendedBenv.add(param.name, operandValues[i]);
        params = params.cdr;
        i++;
      }
      store = store.allocAval(extendedBenva, extendedBenv);
      state = state.setBenva(tid, extendedBenva).setStore(store);
      if (this.body.cdr instanceof Null)
      {
        return kont.unch(new EvalState(this.body.car, tid, state));
      }
      var frame = new BeginKont(application, this.body, tid, state);
      return kont.push(frame, new EvalState(this.body.car, tid, state));
    }
  Closure.prototype.addresses =
    function ()
    {
      return [this.statica];
    }

  function Primitive(name, apply_)
  {
    this.name = name;
    this.apply_ = apply_;
  }
  Primitive.prototype.hashCode =
    function ()
    {
      return this.name.hashCode();
    }
  Primitive.prototype.addresses =
    function ()
    {
      return [];
    }
  Primitive.prototype.toString =
    function ()
    {
      return this.name;
    }

  function Procedure(procs)
  {
    this.procs = procs;
  }
  Procedure.empty =
    function ()
    {
      return new Procedure([]);
    }
  Procedure.from =
    function (procs)
    {
      return new Procedure(procs.slice(0));
    }
  Procedure.prototype.equals =
    function (x)
    {
      if (this === x)
      {
        return true;
      }
      return this.procs.setEquals(x.procs);
    }
  Procedure.prototype.hashCode =
    function ()
    {
      return this.procs.hashCode();
    }
  Procedure.prototype.subsumes =
    function (x)
    {
      if (this === x)
      {
        return true;
      }
      return this.procs.subsumes(x.procs);
    }
  Procedure.prototype.compareTo =
    function (x)
    {
      return Lattice.subsumeComparison(this, x);
    }
  Procedure.prototype.join =
    function (x)
    {
      if (x === BOT)
      {
        return this;
      }
      return new Procedure(Arrays.deleteDuplicates(this.procs.concat(x.procs), Eq.equals));
    }
  Procedure.prototype.addresses =
    function ()
    {
      return this.procs.flatMap(function (proc) {return proc.addresses()});
    }
  Procedure.prototype.apply_ =
    function (application, operandValues, tid, state, kont)
    {
      return this.procs.flatMap(function (proc) {
          return proc.apply_(application, operandValues, tid, state, kont)
      });
    }
  Procedure.prototype.toString =
    function ()
    {
      return "<procedure " + this.procs + ">";
    }

  // install global environment
  var global = Benv.empty();
  var store = new Store();

  function installPrimitive(name, apply_)
  {
    var proca = new ContextAddr(name, 0);
    var procRef = l.abst1(proca);
    var proc = Procedure.from([new Primitive(name, apply_)]);
    global = global.add(name, procRef);
    store = store.allocAval(proca, proc);
  }

  global = global.add("#t", L_TRUE);
  global = global.add("#f", L_FALSE);

  installPrimitive("+",
      function(application, operandValues, tid, state, kont)
      {
        var primValue = operandValues.reduce(function (acc, x) {return p.add(acc, x.prim)}, P_0);
        var value = l.product(primValue, []);
        return kont.pop(function (frame) {
            return new KontState(frame, value, tid, state)
        });
      });
  installPrimitive("-",
      function(application, operandValues, tid, state, kont)
      {
        var primValue = operandValues.slice(1).reduce(function (acc, x) {return p.sub(acc, x.prim)}, operandValues[0].prim);
        var value = l.product(primValue, []);
        return kont.pop(function (frame) {
            return new KontState(frame, value, tid, state)
        });
      });
  installPrimitive("*",
      function(application, operandValues, tid, state, kont)
      {
        var primValue = operandValues.reduce(function (acc, x) {return p.mul(acc, x.prim)}, P_1);
        var value = l.product(primValue, []);
        return kont.pop(function (frame) {
            return new KontState(frame, value, tid, state)
        });
      });
  installPrimitive("=",
      function(application, operandValues, tid, state, kont)
      {
        var primValue = p.eq(operandValues[0].prim, operandValues[1].prim);
        var value = l.product(primValue, []);
        return kont.pop(function (frame) {
            return new KontState(frame, value, tid, state)
        });
      });
  installPrimitive("<",
      function(application, operandValues, tid, state, kont)
      {
        var primValue = p.lt(operandValues[0].prim, operandValues[1].prim)
        var value = l.product(primValue, []);
        return kont.pop(function (frame) {
            return new KontState(frame, value, tid, state)
        });
      });
  installPrimitive("<=",
      function(application, operandValues, tid, state, kont)
      {
        var primValue = p.lte(operandValues[0].prim, operandValues[1].prim)
        var value = l.product(primValue, []);
        return kont.pop(function (frame) {
            return new KontState(frame, value, tid, state)
        });
      });

  var globala = new ContextAddr("global", 0);
  store = store.allocAval(globala, global);

  function InitState(initThread, store)
  {
    this.type = "init";
    this.thread = initThread;
    var threads = HashMap.empty().put(initThread.tid, initThread);
    this.state = new MachineState(threads, store);
    this.store = store;
  }
  InitState.prototype.toString =
    function ()
    {
      return "(init)";
    }
  InitState.prototype.nice =
    function ()
    {
      return "#init";
    }
  InitState.prototype.equals =
    function (x)
    {
      return this.type === x.type &&
        Eq.equals(this.state, x.state);
   }
  InitState.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.state.hashCode();
      return result;
   }
  InitState.prototype.next =
    function (kont)
    {
      var frame = this.thread.context.frame;
      var node = this.thread.context.node;
      return kont.push(frame, new EvalState(node, this.thread.tid, this.state));
    }
  InitState.prototype.addresses =
    function ()
    {
      return this.thread.addresses();
    }
  InitState.prototype.setStore =
    function (store)
    {
      return new InitState(this.thread, store);
    }

  function EvalState(node, tid, state)
  {
    this.type = "eval";
    this.node = node;
    this.tid = tid;
    this.state = state;
    this.store = state.store;
    var thread = state.threads.get(tid, null);
    assertDefinedNotNull(thread);
    this.thread = thread;
  }
  EvalState.prototype.toString =
    function ()
    {
      return "#eval " + this.tid + " " + this.thread.context.node.tag;
    }
  EvalState.prototype.nice =
    function ()
    {
      return "#eval " + this.tid + " " + this.thread.context.node.tag;
    }
  EvalState.prototype.equals =
    function (x)
    {
      return (x instanceof EvalState)
        && this.tid === x.tid
        && Eq.equals(this.state, x.state);
    }
  EvalState.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.tid
      result = prime * result + this.state.hashCode();
      return result;
    }
  EvalState.prototype.next =
    function (kont)
    {
      return evalNode(this.node, this.tid, this.state, kont);
    }
  EvalState.prototype.addresses =
    function ()
    {
      return this.thread.addresses();
    }
  EvalState.prototype.setStore =
    function (store)
    {
      var state = this.state.setStore(store);
      return new EvalState(this.node, this.tid, state);
    }

  var kcc = 0;
  function KontState(tid, frame, value, state)
  {
    this.type = "kont";
    this.frame = frame;
    this.value = value;
    // assert(state instanceof MachineState);

    // TODO: store the value returned by the continuation somewhere in
    // the state, and use it later
    // this.state = state.storeKontValue(tid, value);
    // this.state = state
    this.store = this.state.store;
    this.age = kcc++;
  }
  KontState.prototype.equals =
    function (x)
    {
      return (x instanceof KontState)
        && Eq.equals(this.frame, x.frame)
        && Eq.equals(this.value, x.value)
        && Eq.equals(this.state, x.state)
    }
  KontState.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.frame.hashCode();
      result = prime * result + this.value.hashCode();
      result = prime * result + this.state.hashCode();
      return result;
    }
  KontState.prototype.toString =
    function ()
    {
      return "#kont-" + this.frame;
    }
  KontState.prototype.nice =
    function ()
    {
      return "#kont-" + this.frame.toString();
    }
  KontState.prototype.next =
    function (kont)
    {
      // We can either continue executing this thread, or execute
      // another thread
      return applyKont(this.frame, this.value, this.store, kont)
    }
  KontState.prototype.addresses =
    function ()
    {
      return this.frame.addresses().concat(this.value.addresses());
    }
  KontState.prototype.setStore =
    function (store)
    {
      return new KontState(this.frame, this.value, store);
    }

  function DefineKont(node, tid, state)
  {
    this.node = node;
    this.tid = tid;
    this.state = state;
  }
  DefineKont.prototype.equals =
    function (x)
    {
      return x instanceof DefineKont
        && this.node === x.node
        && thit.tid === x.tid
        && Eq.equals(this.state, x.state);
    }
  DefineKont.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.tid;
      result = prime * result + this.state.hashCode();
      return result;
    }
  DefineKont.prototype.toString =
    function ()
    {
      return "def-" + this.tid + "-" + this.node.tag;
    }
  DefineKont.prototype.nice =
    function ()
    {
      return this.toString()
    }
  DefineKont.prototype.addresses =
    function ()
    {
      var benva = this.state.getBenva(this.tid);
      return [benva];
    }
  DefineKont.prototype.apply =
    function (value, store, kont)
    {
      var node = this.node;
      var benva = this.state.getBenva(this.tid);
      var store = this.state.store;
      var id = node.cdr.car.name;
      var benv = store.lookupAval(benva);
      benv = benv.add(id, value);
      store = store.updateAval(benva, benv); // side-effect
      state = state.setStore(store);
      return kont.pop(function (frame) {
          return new KontState(frame, value, id, state)
      });
    }

  function OperatorKont(node, benva)
  {
    this.node = node;
    this.benva = benva;
  }
  OperatorKont.prototype.equals =
    function (x)
    {
      return x instanceof OperatorKont
        && this.node === x.node
        && Eq.equals(this.benva, x.benva);
    }
  OperatorKont.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.benva.hashCode();
      return result;
    }
  OperatorKont.prototype.toString =
    function ()
    {
      return "rator-" + this.node.tag;
    }
  OperatorKont.prototype.nice =
    function ()
    {
      return "rator-" + this.node.tag;
    }
  OperatorKont.prototype.addresses =
    function ()
    {
      return [this.benva];
    }
  OperatorKont.prototype.apply =
    function (operatorValue, tid, state, kont)
    {
      var node = this.node;
      var benva = this.benva;
      var operands = node.cdr;
      state = state.setBenva(tid, benva);

      if (operands instanceof Null)
      {
        return applyProc(node, operatorValue, [], tid, state, kont);
      }
      var frame = new OperandsKont(node, operands, operatorValue, [], benva);
      return kont.push(frame, new EvalState(operands.car, tid, state));
    }

  function OperandsKont(node, operands, operatorValue, operandValues, benva)
  {
    this.node = node;
    this.operands = operands;
    this.operatorValue = operatorValue;
    this.operandValues = operandValues;
    this.benva = benva;
  }
  OperandsKont.prototype.equals =
    function (x)
    {
      return x instanceof OperandsKont
        && this.node === x.node
        && this.operands === x.operands
        && Eq.equals(this.operatorValue, x.operatorValue)
        && Eq.equals(this.operandValues, x.operandValues)
        && Eq.equals(this.benva, x.benva)
    }
  OperandsKont.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.operands.hashCode();
      result = prime * result + this.operatorValue.hashCode();
      result = prime * result + this.operandValues.hashCode();
      result = prime * result + this.benva.hashCode();
      return result;
    }
  OperandsKont.prototype.toString =
    function ()
    {
      return "rand-" + this.node.tag + "-" + this.operands.tag;
    }
  OperandsKont.prototype.nice =
    function ()
    {
      return "rand-" + this.node.tag + "-" + this.operands.tag;
    }
  OperandsKont.prototype.addresses =
    function ()
    {
      return [this.benva]
        .concat(this.operatorValue.addresses())
        .concat(this.operandValues.flatMap(function (value) {return value.addresses()}));
    }
  OperandsKont.prototype.apply =
    function (operandValue, tid, state, kont)
    {
      var node = this.node;
      var benva = this.benva;
      var operatorValue = this.operatorValue;
      var operandValues = this.operandValues.addLast(operandValue);
      var operands = this.operands.cdr;
      state = state.setBenva(tid, benva);

      if (operands instanceof Null)
      {
        return applyProc(node, operatorValue, operandValues, tid, state, kont);
      }
      var frame = new OperandsKont(node, operands, operatorValue, operandValues, benva);
      return kont.push(frame, new EvalState(operands.car, tid, state));
    }

  function BeginKont(node, exps, benva)
  {
    this.node = node;
    this.exps = exps;
    this.benva = benva;
  }
  BeginKont.prototype.equals =
    function (x)
    {
      return (x instanceof BeginKont)
        && this.node === x.node
        && this.exps === x.exps
        && Eq.equals(this.benva, x.benva);
    }
  BeginKont.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.exps.hashCode();
      result = prime * result + this.benva.hashCode();
      return result;
    }
  BeginKont.prototype.toString =
    function ()
    {
      return "begin-" + this.node.tag + "-" + this.exps.tag;
    }
  BeginKont.prototype.nice =
    function ()
    {
      return "begin-" + this.node.tag + "-" + this.exps.tag;
    }
  BeginKont.prototype.addresses =
    function ()
    {
      return [this.benva];
    }
  BeginKont.prototype.apply =
    function (value, tid, state, kont)
    {
      var node = this.node;
      var benva = this.benva;
      var exps = this.exps.cdr;
      state = state.setBenva(tid, benva);

      if (exps.cdr instanceof Null)
      {
        return kont.unch(new EvalState(exps.car, tid, state));
      }
      var frame = new BeginKont(node, exps, benva);
      return kont.push(frame, new EvalState(exps.car, tid, state));
    }

  function IfKont(node, benva)
  {
    this.node = node;
    this.benva = benva;
  }
  IfKont.prototype.equals =
    function (x)
    {
      return x instanceof IfKont
        && this.node === x.node
        && Eq.equals(this.benva, x.benva);
    }
  IfKont.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.benva.hashCode();
      return result;
    }
  IfKont.prototype.toString =
    function ()
    {
      return "if-" + this.node.tag;
    }
  IfKont.prototype.nice =
    function ()
    {
      return "if-" + this.node.tag;
    }
  IfKont.prototype.addresses =
    function ()
    {
      return [this.benva];
    }
  IfKont.prototype.apply =
    function (conditionValue, tid, state, kont)
    {
      var node = this.node;
      var benva = this.benva;
      state = state.setBenva(tid, benva);
      var consequent = node.cdr.cdr.car;
      var alternate = node.cdr.cdr.cdr.car;
      var falseProj = conditionValue.meet(L_FALSE);
      if (falseProj === BOT) // no false in value
      {
        return evalNode(consequent, benva, store, kont);
      }
      else if (conditionValue.equals(falseProj)) // value is false
      {
//        if (alternate === null)
//        {
//          return kont.pop(function (frame) {return new KontState(frame, L_UNDEFINED, store)});
//        }
        return evalNode(alternate, tid, state, kont);
      }
      else // value > false
      {
        var consequentState = kont.unch(new EvalState(consequent, tid, state));
        var alternateState;
//        if (alternate === null)
//        {
//          alternateState = kont.pop(function (frame) {return new KontState(frame, L_UNDEFINED, store)});
//        }
//        else
//        {
          alternateState = kont.unch(new EvalState(alternate, tid, state));
//        }
        return consequentState.concat(alternateState);
      }
    }

  function SetKont(node, benva)
  {
    this.node = node;
    this.benva = benva;
  }
  SetKont.prototype.equals =
    function (x)
    {
      return x instanceof SetKont
        && this.node === x.node
        && Eq.equals(this.benva, x.benva);
    }
  SetKont.prototype.hashCode =
    function ()
    {
      var prime = 7;
      var result = 1;
      result = prime * result + this.node.hashCode();
      result = prime * result + this.benva.hashCode();
      return result;
    }
  SetKont.prototype.toString =
    function ()
    {
      return "set-" + this.node.tag;
    }
  SetKont.prototype.addresses =
    function ()
    {
      return [this.benva];
    }
  SetKont.prototype.apply =
    function (value, tid, state, kont)
    {
      var node = this.node;
      var benva = this.benva;
      var store = state.store;
      state = state.setBenva(tid, benva);
      var id = node.cdr.car;
      var name = id.name;

      var as = [];
      var todo = [benva];
      var visited = HashSet.empty();
      /* find the benvs where id is bound */
      while (todo.length > 0)
      {
        var a = todo.shift();
        if (visited.contains(a))
        {
          continue;
        }
        visited = visited.add(a);
        var benv = store.lookupAval(a);
        var lookupValue = benv.lookup(name);
        if (lookupValue !== BOT)
        {
          as.push(a);
        }
        var parentas = benv.parentas;
        todo = todo.concat(parentas);
      }
      if (as.length === 0)
      {
        throw new Error("cannot set! an undefined identifier");
      }
      /* update the values */
      while (as.length > 0)
      {
        var a = as.shift();
        var benv = store.lookupAval(a);
        benv = benv.add(name, value);
        store = store.updateAval(a, benv);
      }
      state = state.setStore(store);
      return kont.pop(function (frame) {
        return new KontState(frame, L_UNDEFINED, tid, state)
      });
    }

  function evalLiteral(node, tid, state, kont)
  {
    var value = l.abst1(node.valueOf());
    return kont.pop(function (frame) {
        return new KontState(tid, frame, value, state)
    });
  }

  function evalLambda(node, tid, state, kont)
  {
    var benva = state.getBenva(tid);
    var store = state.store;
    var closure = new Closure(node, benva, node.cdr.car, node.cdr.cdr);
    var closurea = a.closure(node, benva, store, kont);
    var closureRef = l.abst1(closurea);
    store = store.allocAval(closurea, Procedure.from([closure]));
    return kont.pop(function (frame) {
        return new KontState(tid, frame, closureRef, state)
    });
  }

  function evalQuote(node, tid, state, kont)
  {
    var value = l.abst1(node.cdr.car);
    return kont.pop(function (frame) {
        return new KontState(tid, frame, value, state)
    });
  }

  function evalDefine(node, tid, state, kont)
  {
    var benva = state.getBenva(tid);
    var lval = node.cdr.car;
    if (lval instanceof Pair)
    {
      throw new Error("TODO");
    }
    var exp = node.cdr.cdr.car;
    var frame = new DefineKont(node, tid, state);
    return kont.push(frame, new EvalState(node, tid, state));
  }

  function evalIdentifier(node, tid, state, kont)
  {
    var benva = state.getBenva(tid);
    var store = state.store;
    var name = node.name;
    var todo = [benva];
    var visited = HashSet.empty();
    var value = BOT;
    while (todo.length > 0)
    {
      var a = todo.shift();
      if (visited.contains(a))
      {
        continue;
      }
      visited = visited.add(a);
      var benv = store.lookupAval(a);
      var lookupValue = benv.lookup(name);
      if (lookupValue !== BOT)
      {
        value = value.join(lookupValue);
        continue;
      }
      var parentas = benv.parentas;
      todo = todo.concat(parentas);
    }
    if (value === BOT)
    {
      throw new Error("undefined: " + node);
    }
    return kont.pop(function (frame) {
        return new KontState(tid, frame, value, state)
    });
  }

  function evalBegin(node, tid, state, kont)
  {
    var exps = node.cdr;
    if (exps instanceof Null)
    {
      return kont.pop(function (frame) {
          return new KontState(tid, frame, L_UNDEFINED, state)
      });
    }
    if (exps.cdr instanceof Null)
    {
      return kont.unch(new EvalState(node, tid, state));
    }
    var frame = new BeginKont(node, exps, tid, state);
    return kont.push(frame, new EvalState(exps.car, tid, state));
  }

  function evalSet(node, tid, state, kont)
  {
    if (node.cdr instanceof Null || node.cdr.cdr instanceof Null ||
        node.cdr.car instanceof Pair)
    {
      throw new Error("invalid set!: " + node);
    }
    var id = node.cdr.car;
    var exp = node.cdr.cdr.car;
    var frame = new SetKont(node, tid, store);
    return kont.push(frame, new EvalState(exp, tid, state))
  }

  function applyProc(node, operatorValue, operandValues, tid, state, kont)
  {
    var store = state.store;
    var operatorAs = operatorValue.addresses();
    if (operatorAs.length === 0)
    {
      throw new Error("not an operator: " + node.car);
    }
    return operatorAs.flatMap(
      function (operatora)
      {
        var proc = store.lookupAval(operatora);
        return proc.apply_(node, operandValues, tid, state, kont);
      })
  }

  function applyKont(frame, value, tid, state, kont)
  {
    if (frame.isMarker)
    {
      return kont.pop(function (frame) {
          return new KontState(frame, value, tid, state)
      });
    }
    return frame.apply(value, tid, state, kont);
  }

  function evalIf(node, tid, state, kont)
  {
    var condition = node.cdr.car;
    var frame = new IfKont(node, tid, state);
    return kont.push(frame, new EvalState(condition, tid, state));
  }

  function evalApplication(node, tid, state, kont)
  {
    var operator = node.car;
    var frame = new OperatorKont(node, tid, state);
    return kont.push(frame, new EvalState(operator, tid, state));
  }

  function evalNode(node, tid, state, kont)
  {
    if (node instanceof Number || node instanceof Boolean || node instanceof String || node instanceof Null)
    {
      return evalLiteral(node, tid, state, kont);
    }
    if (node instanceof Sym)
    {
      return evalIdentifier(node, tid, state, kont);
    }
    if (node instanceof Pair)
    {
      var car = node.car;
      if (car instanceof Sym)
      {
        var name = car.name;
        if (name === "lambda")
        {
          return evalLambda(node, tid, state, kont);
        }
        if (name === "define")
        {
          return evalDefine(node, tid, state, kont);
        }
        if (name === "if")
        {
          return evalIf(node, tid, state, kont);
        }
        if (name === "quote")
        {
          return evalQuote(node, tid, state, kont);
        }
        if (name === "begin")
        {
          return evalBegin(node, tid, state, kont);
        }
        if (name === "set!")
        {
          return evalSet(node, tid, state, kont);
        }
      }
      return evalApplication(node, tid, state, kont);
    }
    throw new Error("cannot handle node " + node);
  }

  var module = {};
  // TODO: module.evalState does not seem to be needed anywhere
  module.p = p;
  module.l = l;
  module.store = store;
  module.globala = globala;

  module.inject =
    function (node, override)
    {
      override = override || {};
      var benva = override.benva || globala;
      var haltFrame = new HaltKont([benva]);
      var initThread = new Thread(t.t0, new Context(node, benva, haltFrame, h.h0));
      return new InitState(initThread, override.store || store);
    }

  return module;
}
