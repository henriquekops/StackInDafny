class {:autocontracts} Stack
{
    // Abstraction
    ghost const MAXSIZE: nat;
    ghost var content: seq<int>;

    // Implementation
    var a: array<int>;
    var cursor: nat;
    const max: nat;

    // Class invariant
    predicate Valid()
    reads this
    {
        max > 0
        && a.Length == max
        && 0 <= cursor <= max
        && MAXSIZE == max
        && content == a[0..cursor]
    }
    
    constructor (s: nat)
    requires s > 0
    ensures s == MAXSIZE
    ensures content == []
    ensures cursor == 0
    {
        MAXSIZE := s;
        max := s;
        a := new int[s];
        cursor := 0;
        content := [];
    }


    // add: bool
    method add(e:int) returns (b: bool)
    requires |content| < MAXSIZE
    ensures content == old(content) + [e]
    {
        var full := isFull();
        if full{
            b := false;
        } else {
            a[cursor] := e;
            cursor := cursor + 1;
            content := content + [e];
            b := true;
        }
    }

    // pop: int
    method pop() returns (e: int)
    requires |content| > 0
    ensures e == old(content)[|old(content)| - 1]
    ensures content == old(content)[0..|old(content)| - 1]
    {
        e := a[cursor - 1];
        cursor := cursor - 1;
        content := a[..cursor];
    }

    // peek: int
    method peek() returns (e: int)
    requires |content| > 0
    ensures content == old(content)
    ensures e == old(content)[|content|-1]
    {
        e := a[cursor-1];
    }

    // isFull: bool
    method isFull() returns (b: bool)
    ensures content == old(content)
    ensures b == (|content| == MAXSIZE) //???
    {
        b := max == cursor;
    }

    // isEmpty: bool
    method isEmpty() returns (b: bool)
    ensures content == old(content)
    ensures b == (|content| == 0)
    {
        b := cursor == 0;
    }
    
    // howMany: nat
    method howMany() returns (m: nat)
    ensures content == old(content)
    ensures m == |content|
    {
        m := cursor;
    }

    // maxSize: nat
    method maxSize() returns (m: nat)
    ensures content == old(content)
    ensures m == MAXSIZE
    {
        m := max;
    }

    // invert: void
    method invert()
    requires |content| > 0
    ensures |content| == |old(content)|
    ensures forall i | 0 <= i < |content| :: content[i] == old(content[|content| - i - 1]);
    {
        var i := 0;
        var b := new int[max];
        
        forall i | 0 <= i < cursor
        {
            b[i] := a[cursor - i - 1];
        }

        a := b;
        content := a[..cursor];
    }

    // show: void
    method show()
    ensures old(content) == content
    {
        print(a[..cursor]);
        print("\n");
    }

}

method Main()
{
    var stack := new Stack(10);

    var a := stack.add(1);
    var b := stack.add(2);
    var c := stack.add(3);

    var q := stack.howMany();
    assert q == 3;
    var w := stack.maxSize();
    assert w == 10;
    var r := stack.peek();
    assert r == 3;

    var d := stack.add(4);
    var e := stack.add(5);
    var f := stack.add(6);
    var g := stack.add(7);

    r := stack.peek();
    assert r == 7;

    stack.show();
    stack.invert();
    stack.show();

    r := stack.peek();
    assert r == 1;

    var p := stack.pop();
    assert p == 1;

    r := stack.peek();
    assert r == 2;

    stack.show();
}
