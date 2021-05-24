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
    requires 0 <= cursor <= MAXSIZE
    requires |content| > 0
    ensures cursor == old(cursor)
    modifies this
    {
        var i, j := 0, cursor - 1;
        while i < j
        invariant 0 <= i <= j <= MAXSIZE;
        invariant cursor == old(cursor);
        {
            a[i], a[j] := a[j], a[i];
            i, j := i + 1, j - 1;
        }
        content := a[0..cursor];
    }

    method invert2()
    requires |content| > 0
    {
        var i := 0;
        var b := new int[max];

        while i < cursor
        invariant old(a) == a;
        invariant old(cursor) == cursor;
        {
            b[i] := a[cursor - i - 1];
            i := i + 1;
        }
        a := b;
        content := a[0..cursor];
        assert content == a[0..cursor];
        assert max > 0;
        assert a.Length == max;
        assert 0 <= cursor <= max;
        assert MAXSIZE == max;
        assert content == a[0..cursor];
    }

    // show: void
    method show()
    {
        print(a);
    }

}

method Main()
{
    var stack := new Stack(10);

    var a := stack.add(2);
    var b := stack.add(8);
    var c := stack.add(10);

    var q := stack.howMany();
    assert q == 3;
    var w := stack.maxSize();
    assert w == 10;
    var e := stack.peek();
    assert e == 10;
}
