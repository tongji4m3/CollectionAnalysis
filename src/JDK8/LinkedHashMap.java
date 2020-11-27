package java.util;

import java.io.IOException;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;

/*
模板模式

每次插入数据，或者访问、修改数据时，会增加节点、或调整链表的节点顺序。以决定迭代时输出的顺序。

accessOrder ,默认是false，则迭代时输出的顺序是插入节点的顺序。
若为true，则输出的顺序是按照访问节点的顺序。为true时，可以在这基础之上构建一个LruCache.

LinkedHashMap并没有重写任何put方法。但是其重写了构建新节点的newNode()方法.在每次构建新节点时，将新节点链接在内部双向链表的尾部

在HashMap的插入删除等操作后会调用钩子方法(afterNodeAccess, afterNodeInsertion, afterNodeRemoval)，
而这些方法的实现就在LinkedHashMap中，这些方法的目的就是操作 before 和 after 指针。

　　LinkedHashMap 重写newNode，newTreeNode 方法，这两个方法是在插入时HashMap构建新节点时调用的，
对于重写后的newNode 先是创建LinkedHashMap#Entry节点，之后将其加到 before/after 链的尾部；

　　对于重写后的newTreeNode 先是创建HashMap的TreeNode节点，因为其继承自LinkedHashMap#Entry，
所以含有before/after 指针，之后同样加入到链尾。

accessOrder=true的模式下,在afterNodeAccess()函数中，会将当前被访问到的节点e，移动至内部的双向链表的尾部。
值得注意的是，afterNodeAccess()函数中，会修改modCount,因此当你正在accessOrder=true的模式下,
迭代LinkedHashMap时，如果同时查询访问数据，也会导致fail-fast，因为迭代的顺序已经改变。

通过维护一个运行于所有条目的双向链表，LinkedHashMap保证了元素迭代的顺序。该迭代顺序可以是插入顺序或者是访问顺序

LinkedHashMap可以认为是HashMap+LinkedList，即它既使用HashMap操作数据结构，又使用LinkedList维护插入元素的先后顺序。

LinkedHashMap虽然逻辑上有两套,但实际上是通过引用指向而形成的head,tail链表(他们拿node节点链接而形成),实际上也只有一份数据

注意该循环双向链表的头部存放的是最久访问的节点或最先插入的节点，尾部为最近访问的或最近插入的节点，迭代器遍历方向是从链表的头部开始到链表尾部结束，在链表尾部有一个空的header节点，该节点不存放key-value内容，为LinkedHashMap类的成员属性，循环双向链表的入口。
 */

/**
 * 保持双向链表,保持插入顺序
 * Map m = Collections.synchronizedMap(new LinkedHashMap(...))
 * fail-fast
 */
public class LinkedHashMap<K, V>
        extends HashMap<K, V>
        implements Map<K, V> {

    /**
     * HashMap.Node subclass for normal LinkedHashMap entries.
     */
    //多了指向前面的,后面的指针
    //before 与 after 提供了一种视图，从该角度看是一个所有节点按插入顺序排列的双向链表。
    //维护双向链表
    static class Entry<K, V> extends HashMap.Node<K, V> {
        Entry<K, V> before, after;

        Entry(int hash, K key, V value, Node<K, V> next) {
            super(hash, key, value, next);
        }
    }

    private static final long serialVersionUID = 3801124242820219131L;

    /**
     * The head (eldest) of the doubly linked list.
     */
    transient LinkedHashMap.Entry<K, V> head;

    /**
     * The tail (youngest) of the doubly linked list.
     */
    transient LinkedHashMap.Entry<K, V> tail;

    /**
     * The iteration ordering method for this linked hash map: <tt>true</tt>
     * for access-order, <tt>false</tt> for insertion-order.
     *
     * @serial
     */
    //LRU顺序,插入顺序
    final boolean accessOrder;

    // internal utilities

    // link at the end of list
    //将新增的节点，连接在链表的尾部
    private void linkNodeLast(LinkedHashMap.Entry<K, V> p) {
        LinkedHashMap.Entry<K, V> last = tail;
        tail = p;
        if (last == null)
            head = p;
        else {//将新节点连接在链表的尾部
            p.before = last;
            last.after = p;
        }
    }

    // apply src's links to dst
    //替换节点的方法，我们使用的replacementNode，replacementTreeNode等方法都是通过该方法实现的
    //用dst元素（新创建的元素）替换链表中的src元素（链表中的原有元素），
    // 并将src元素的before、after节点转移到dst元素,可以看出这是一个替换操作，使用新元素替换旧元素。
    private void transferLinks(LinkedHashMap.Entry<K, V> src,
                               LinkedHashMap.Entry<K, V> dst) {
        LinkedHashMap.Entry<K, V> b = dst.before = src.before;
        LinkedHashMap.Entry<K, V> a = dst.after = src.after;
        if (b == null)
            head = dst;
        else
            b.after = dst;
        if (a == null)
            tail = dst;
        else
            a.before = dst;
    }

    // overrides of HashMap hook methods
    //重写以便初始化双向列表
    //即全部清空
    void reinitialize() {
        super.reinitialize();
        head = tail = null;
    }

    //新建一个节点,并且链接到最后一个位置上
    //注意,这是重写了HashMap的newNode方法,这样基本创建节点都会用到了
    /*
    newNode()会在HashMap的putVal()方法里被调用，putVal()方法会在批量插入数据
    putMapEntries(Map<? extends K, ? extends V> m, boolean evict)或者插入单个数据public V put(K key, V value)时被调用
     */
    Node<K, V> newNode(int hash, K key, V value, Node<K, V> e) {
        LinkedHashMap.Entry<K, V> p =
                new LinkedHashMap.Entry<K, V>(hash, key, value, e);
        //在每次构建新节点时，通过linkNodeLast(p);将新节点链接在内部双向链表的尾部。
        linkNodeLast(p);
        return p;
    }

    //当由红黑树转换成单向链表时，将原来的TreeNode转换成单向链表Node
    Node<K, V> replacementNode(Node<K, V> p, Node<K, V> next) {
        LinkedHashMap.Entry<K, V> q = (LinkedHashMap.Entry<K, V>) p;
        LinkedHashMap.Entry<K, V> t =
                new LinkedHashMap.Entry<K, V>(q.hash, q.key, q.value, next);
        transferLinks(q, t);
        return t;
    }

    // 插入元素时，构造一个红黑树节点元素TreeNode
    TreeNode<K, V> newTreeNode(int hash, K key, V value, Node<K, V> next) {
        TreeNode<K, V> p = new TreeNode<K, V>(hash, key, value, next);
        linkNodeLast(p);
        return p;
    }

    //当单向链表转换为红黑树时，将原来的单向链表Node转换为TreeNode
    TreeNode<K, V> replacementTreeNode(Node<K, V> p, Node<K, V> next) {
        LinkedHashMap.Entry<K, V> q = (LinkedHashMap.Entry<K, V>) p;
        TreeNode<K, V> t = new TreeNode<K, V>(q.hash, q.key, q.value, next);
        transferLinks(q, t);
        return t;
    }

    //正常的断开链条
    //从链式关系中删除节点e
    //该方法会在Node<K,V> removeNode(int hash, Object key, Object value, boolean matchValue, boolean movable)方法中回调
    void afterNodeRemoval(Node<K, V> e) { // unlink
        LinkedHashMap.Entry<K, V> p =
                (LinkedHashMap.Entry<K, V>) e, b = p.before, a = p.after;
        //待删除节点 p 的前置后置节点都置空
        p.before = p.after = null;
        //如果前置节点是null，则现在的头结点应该是后置节点a
        if (b == null)
            head = a;
        else//否则将前置节点b的后置节点指向a
            b.after = a;
        //该元素是尾元素
        if (a == null)
            tail = b;
        else
            a.before = b;
    }

    //元素插入后，可能会删除最旧的、访问次数最少的元素，也就是头节点
    //按需删除最早插入的一个元素
    //回调函数，新节点插入之后回调 ， 根据evict判断是否需要删除最老插入的节点。如果实现LruCache会用到这个方法。
    void afterNodeInsertion(boolean evict) { // possibly remove eldest
        LinkedHashMap.Entry<K, V> first;
        //removeEldestEntry默认返回false，可以被子类改写，如果实现LRU Cache，可以返回true
        //把最老的没有被访问的元素移除掉
        if (evict && (first = head) != null && removeEldestEntry(first)) {
            K key = first.key;
            removeNode(hash(key), key, null, false, true);
        }
    }

    //访问的元素如果不是尾节点，那么就把它与尾节点交换，所以随着元素的访问，访问次数越多的元素越靠后
    //通过afterNodeAccess方法维护访问顺序，每次访问该元素就将该元素移动到双向链表的末尾
    void afterNodeAccess(Node<K, V> e) { // move node to last
        LinkedHashMap.Entry<K, V> last;
        //如果是按照访问元素顺序遍历，将该元素移到到最后一个，注意要求该元素不能是最后一个元素
        if (accessOrder && (last = tail) != e) {
            //节点e强转成双向链表节点p
            LinkedHashMap.Entry<K, V> p =
                    (LinkedHashMap.Entry<K, V>) e, b = p.before, a = p.after;
            //p现在是尾节点， 后置节点一定是null
            p.after = null;
            //如果p的前置节点是null，则p以前是头结点，所以更新现在的头结点是p的后置节点a
            if (b == null)
                head = a;
            else//否则更新p的前直接点b的后置节点为 a
                b.after = a;
            //该元素不是尾元素
            if (a != null)
                a.before = b;
            else
                last = b;
            if (last == null)
                head = p;
            else {
                p.before = last;
                last.after = p;
            }
            //尾节点的引用赋值成p
            tail = p;
            //注意此时modCount会自增
            ++modCount;
        }
    }

    void internalWriteEntries(java.io.ObjectOutputStream s) throws IOException {
        for (LinkedHashMap.Entry<K, V> e = head; e != null; e = e.after) {
            s.writeObject(e.key);
            s.writeObject(e.value);
        }
    }

    /**
     * Constructs an empty insertion-ordered <tt>LinkedHashMap</tt> instance
     * with the specified initial capacity and load factor.
     *
     * @param initialCapacity the initial capacity
     * @param loadFactor      the load factor
     * @throws IllegalArgumentException if the initial capacity is negative
     *                                  or the load factor is nonpositive
     */
    public LinkedHashMap(int initialCapacity, float loadFactor) {
        super(initialCapacity, loadFactor);
        //默认是插入顺序
        //按照调用put方法插入的顺序进行排序的
        accessOrder = false;
    }

    /**
     * Constructs an empty insertion-ordered <tt>LinkedHashMap</tt> instance
     * with the specified initial capacity and a default load factor (0.75).
     *
     * @param initialCapacity the initial capacity
     * @throws IllegalArgumentException if the initial capacity is negative
     */
    public LinkedHashMap(int initialCapacity) {
        super(initialCapacity);
        accessOrder = false;
    }

    /**
     * Constructs an empty insertion-ordered <tt>LinkedHashMap</tt> instance
     * with the default initial capacity (16) and load factor (0.75).
     */
    public LinkedHashMap() {
        super();
        accessOrder = false;
    }


    public LinkedHashMap(Map<? extends K, ? extends V> m) {
        super();
        accessOrder = false;
        putMapEntries(m, false);
    }


    //能指定accessOrder的值
    public LinkedHashMap(int initialCapacity,
                         float loadFactor,
                         boolean accessOrder) {
        super(initialCapacity, loadFactor);
        this.accessOrder = accessOrder;
    }



    /*
    由于LinkedHashMap维护了一个双向链表，因此它的containsValue(value)方法直接
    遍历双向链表查找对应的Entry即可，而无需去遍历哈希桶。
     */
    public boolean containsValue(Object value) {
        for (LinkedHashMap.Entry<K, V> e = head; e != null; e = e.after) {
            V v = e.value;
            if (v == value || (value != null && value.equals(v)))
                return true;
        }
        return false;
    }


    public V get(Object key) {
        Node<K, V> e;
        //调用父类的get方法
        if ((e = getNode(hash(key), key)) == null)
            return null;
//        当 accessOrder = true 时，即表示按照最近访问的迭代顺序，会将访问过的元素放在链表后面。
        if (accessOrder)
            afterNodeAccess(e);
        return e.value;
    }

    /**
     * {@inheritDoc}
     */
    public V getOrDefault(Object key, V defaultValue) {
        Node<K, V> e;
        if ((e = getNode(hash(key), key)) == null)
            return defaultValue;
        //这个也算是访问了
        if (accessOrder)
            afterNodeAccess(e);
        return e.value;
    }

    /**
     * {@inheritDoc}
     */
    public void clear() {
        super.clear();
        head = tail = null;
    }


    //LinkedHashMap 默认返回false 则不删除节点。 返回true 代表要删除最早的节点。通常构建一个LruCache会在达到Cache的上限是返回true
    //是构建LruCache需要的回调
    //一般新加一个时可能要删除
    protected boolean removeEldestEntry(Map.Entry<K, V> eldest) {
        return false;
    }


    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new LinkedKeySet();
            keySet = ks;
        }
        return ks;
    }

    final class LinkedKeySet extends AbstractSet<K> {
        public final int size() {
            return size;
        }

        public final void clear() {
            LinkedHashMap.this.clear();
        }

        public final Iterator<K> iterator() {
            return new LinkedKeyIterator();
        }

        public final boolean contains(Object o) {
            return containsKey(o);
        }

        public final boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }

        public final Spliterator<K> spliterator() {
            return Spliterators.spliterator(this, Spliterator.SIZED |
                    Spliterator.ORDERED |
                    Spliterator.DISTINCT);
        }

        public final void forEach(Consumer<? super K> action) {
            if (action == null)
                throw new NullPointerException();
            int mc = modCount;
            for (LinkedHashMap.Entry<K, V> e = head; e != null; e = e.after)
                action.accept(e.key);
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  If the map is
     * modified while an iteration over the collection is in progress
     * (except through the iterator's own <tt>remove</tt> operation),
     * the results of the iteration are undefined.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Collection.remove</tt>, <tt>removeAll</tt>,
     * <tt>retainAll</tt> and <tt>clear</tt> operations.  It does not
     * support the <tt>add</tt> or <tt>addAll</tt> operations.
     * Its {@link Spliterator} typically provides faster sequential
     * performance but much poorer parallel performance than that of
     * {@code HashMap}.
     *
     * @return a view of the values contained in this map
     */
    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new LinkedValues();
            values = vs;
        }
        return vs;
    }

    final class LinkedValues extends AbstractCollection<V> {
        public final int size() {
            return size;
        }

        public final void clear() {
            LinkedHashMap.this.clear();
        }

        public final Iterator<V> iterator() {
            return new LinkedValueIterator();
        }

        public final boolean contains(Object o) {
            return containsValue(o);
        }

        public final Spliterator<V> spliterator() {
            return Spliterators.spliterator(this, Spliterator.SIZED |
                    Spliterator.ORDERED);
        }

        public final void forEach(Consumer<? super V> action) {
            if (action == null)
                throw new NullPointerException();
            int mc = modCount;
            for (LinkedHashMap.Entry<K, V> e = head; e != null; e = e.after)
                action.accept(e.value);
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    public Set<Map.Entry<K, V>> entrySet() {
        Set<Map.Entry<K, V>> es;
        return (es = entrySet) == null ? (entrySet = new LinkedEntrySet()) : es;
    }

    final class LinkedEntrySet extends AbstractSet<Map.Entry<K, V>> {
        public final int size() {
            return size;
        }

        public final void clear() {
            LinkedHashMap.this.clear();
        }

        public final Iterator<Map.Entry<K, V>> iterator() {
            return new LinkedEntryIterator();
        }

        //调用HashMap的
        public final boolean contains(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            Object key = e.getKey();
            Node<K, V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }

        //都是调用父类HashMap的删除方法,而那个方法又会回调afterNodeRemoval(node); 所以不用担心
        public final boolean remove(Object o) {
            if (o instanceof Map.Entry) {
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }

        public final Spliterator<Map.Entry<K, V>> spliterator() {
            return Spliterators.spliterator(this, Spliterator.SIZED |
                    Spliterator.ORDERED |
                    Spliterator.DISTINCT);
        }

        public final void forEach(Consumer<? super Map.Entry<K, V>> action) {
            if (action == null)
                throw new NullPointerException();
            int mc = modCount;
            for (LinkedHashMap.Entry<K, V> e = head; e != null; e = e.after)
                action.accept(e);
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    // Map overrides

    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null)
            throw new NullPointerException();
        int mc = modCount;
        for (LinkedHashMap.Entry<K, V> e = head; e != null; e = e.after)
            action.accept(e.key, e.value);
        if (modCount != mc)
            throw new ConcurrentModificationException();
    }

    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null)
            throw new NullPointerException();
        int mc = modCount;
        for (LinkedHashMap.Entry<K, V> e = head; e != null; e = e.after)
            e.value = function.apply(e.key, e.value);
        if (modCount != mc)
            throw new ConcurrentModificationException();
    }

    // Iterators
    //保证迭代顺序为双向链表的顺序
    //从链表头部开始遍历,那么如果插入a,b,c ,则输出还是a,b,c
    //如果是按照访问顺序,插入a,b,c后访问了a,则顺序变为了b,c,a 因为a被插入链表尾部
    abstract class LinkedHashIterator {
        //下一节点
        LinkedHashMap.Entry<K, V> next;
        //当前节点
        LinkedHashMap.Entry<K, V> current;
        int expectedModCount;

        LinkedHashIterator() {
            //从双向链表的头元素开始遍历
            next = head;
            //记录当前modCount，以满足fail-fast
            expectedModCount = modCount;
            //当前节点为null
            current = null;
        }

        public final boolean hasNext() {
            return next != null;
        }

        //nextNode() 就是迭代器里的next()方法 。
        //该方法的实现可以看出，迭代LinkedHashMap，就是从内部维护的双链表的表头开始循环输出
        final LinkedHashMap.Entry<K, V> nextNode() {
            LinkedHashMap.Entry<K, V> e = next;
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            if (e == null)
                throw new NoSuchElementException();
            //按照双向链表而不是哈希数组的顺序遍历
            current = e;
            next = e.after;
            return e;
        }
        //删除方法 最终还是调用了HashMap的removeNode方法
        public final void remove() {
            Node<K, V> p = current;
            if (p == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            current = null;
            K key = p.key;
            removeNode(hash(key), key, null, false, false);
            //迭代器自己删除不算fail-fast
            expectedModCount = modCount;
        }
    }

    final class LinkedKeyIterator extends LinkedHashIterator
            implements Iterator<K> {
        public final K next() {
            return nextNode().getKey();
        }
    }

    final class LinkedValueIterator extends LinkedHashIterator
            implements Iterator<V> {
        public final V next() {
            return nextNode().value;
        }
    }

    final class LinkedEntryIterator extends LinkedHashIterator
            implements Iterator<Map.Entry<K, V>> {
        public final Map.Entry<K, V> next() {
            return nextNode();
        }
    }


}
