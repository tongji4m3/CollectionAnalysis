package JDK8;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

import sun.misc.SharedSecrets;



/*
允许key和value为null
unsynchronized非线程安全的
不保证元素存储的顺序

在将元素适当地分散在存储桶中,可以保证get,put基本操作为O(1)
Iterator的速度与capacity(桶的数量),size(key-value的值)成比例
所以initial capacity不应太高,load factor(负载因子)不应太低

load factor默认为0.75.定义了hash表中在扩容前能装多少.超过则扩容成两倍

如果要存很多键,最好一开始就给大容量
设置大容量可能可以避免resize

不是线程安全的,多线程如果要进行添加删除操作,则要加synchronized
Collections.synchronizedMap(new HashMap(...));也可以实现

迭代器的快速失败机制:在迭代器中修改了结构,则throw ConcurrentModificationException
 */
/*
Cloneable:实现的是浅层次拷贝，即对拷贝对象的改变会影响被拷贝的对象
Serializable:实现了序列化，即可以将HashMap对象保存至本地，之后可以恢复状态
 */
/*
计算索引分三步:
    1. 拿到 key 的 hashCode 值
    2. 将 hashCode 的高位参与运算，重新计算 hash 值
    (将 hashCode 的高 16 位与 hashCode 进行异或运算，主要是为了在 table 的 length 较小的时候，让高位也参与运算
    3. 将计算出来的 hash 值与 (table.length - 1) 进行 & 运算
    (因为x mod 2^n = x & (2^n - 1),而底层数组长度总是 2 的 n 次方,所以x mod table.length = x & (table.length - 1)

扩容后节点重 hash 只可能出现在“原索引位置” 与 “原索引 + oldCap 位置”:
    如16->32
    即hash & 1111 变成 hash & 11111
    可以看到只有最高位可能会改变,即分成 0xxxx 或者 1xxxx,即要不在原索引位置,要不在原索引 + oldCap 位置

jdk1.7死循环:
    导致死循环的主要原因是扩容后，节点的顺序会反掉,即采用头插法造成的

HashMap 和 Hashtable 的区别
    HashMap 允许 key 和 value 为 null，Hashtable 不允许。
    HashMap 的默认初始容量为 16，Hashtable 为 11。
    HashMap 的扩容为原来的 2 倍，Hashtable 的扩容为原来的 2 倍加 1。
    HashMap 是非线程安全的，Hashtable是线程安全的。
    HashMap 的 hash 值重新计算过，Hashtable 直接使用 hashCode。
    HashMap 去掉了 Hashtable 中的 contains 方法。
    HashMap 继承自 AbstractMap 类，Hashtable 继承自 Dictionary 类。

HashMap 有 threshold 属性和 loadFactor 属性，但是没有 capacity 属性。
初始化时，如果传了初始化容量值，该值是存在 threshold 变量，并且 Node 数组是在第一次 put 时才会进行初始化，
初始化时会将此时的 threshold 值作为新表的 capacity 值，然后用 capacity 和 loadFactor 计算新表的真正 threshold 值。

当同一个索引位置的节点在增加后达到8个时，并且此时数组的长度大于等于 64，
则会触发链表节点（Node）转红黑树节点（TreeNode），转成红黑树节点后，其实链表的结构还存在，通过 next 属性维持。
链表节点转红黑树节点的具体方法为源码中的 treeifyBin 方法。而如果数组长度小于64，则不会触发链表转红黑树，而是会进行扩容。
*/
public class HashMap<K, V> extends AbstractMap<K, V>
        implements Map<K, V>, Cloneable, Serializable {

    //序列号
    private static final long serialVersionUID = 362498820763181265L;

    /*
     都是Comparable时用比较来排序树(用反射实现),否则用hashcode.这样在hashCode不均匀的情况下表现较好

     链表中节点个数为8时的概率为 0.00000006


     红黑树的根节点不一定是索引位置的头节点（也就是链表的头节点），
     HashMap 通过 moveRootToFront 方法来维持红黑树的根结点就是索引位置的头结点，
     但是在 removeTreeNode 方法中，当 movable 为 false 时，不会调用 moveRootToFront 方法，
     此时红黑树的根节点不一定是索引位置的头节点，该场景发生在 HashIterator 的 remove 方法中。

     重新分时,保持他们的相互顺序

     为它的子类LinkedHashMap提供一些钩子方法
     */

    /**
     * The default initial capacity - MUST be a power of two.
     */
    // 默认的初始容量是16
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; // aka 16

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<30.
     */
    static final int MAXIMUM_CAPACITY = 1 << 30;

    /**
     * The load factor used when none specified in constructor.
     */
    static final float DEFAULT_LOAD_FACTOR = 0.75f;

    /**
     * The bin count threshold for using a tree rather than list for a
     * bin.  Bins are converted to trees when adding an element to a
     * bin with at least this many nodes. The value must be greater
     * than 2 and should be at least 8 to mesh with assumptions in
     * tree removal about conversion back to plain bins upon
     * shrinkage.
     */
    //至少应该为8以便于退化为链表
    static final int TREEIFY_THRESHOLD = 8;

    /**
     * The bin count threshold for untreeifying a (split) bin during a
     * resize operation. Should be less than TREEIFY_THRESHOLD, and at
     * most 6 to mesh with shrinkage detection under removal.
     */
    static final int UNTREEIFY_THRESHOLD = 6;

    /**
     * The smallest table capacity for which bins may be treeified.
     * (Otherwise the table is resized if too many nodes in a bin.)
     * Should be at least 4 * TREEIFY_THRESHOLD to avoid conflicts
     * between resizing and treeification thresholds.
     */
    // 桶中结构转化为红黑树对应的table的最小大小
    static final int MIN_TREEIFY_CAPACITY = 64;

    /**
     * Basic hash bin node, used for most entries.  (See below for
     * TreeNode subclass, and in LinkedHashMap for its Entry subclass.)
     */
    /*
    Map.Entry是Map的一个内部接口。表示Map中的一个实体（一个key-value对）。接口中有getKey(),getValue方法。
     */
    static class Node<K, V> implements Map.Entry<K, V> {
        final int hash;
        final K key;
        V value;
        HashMap.Node<K, V> next;

        Node(int hash, K key, V value, HashMap.Node<K, V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        public final K getKey() {
            return key;
        }

        public final V getValue() {
            return value;
        }

        public final String toString() {
            return key + "=" + value;
        }

        public final int hashCode() {
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }

        public final V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        public final boolean equals(Object o) {
            if (o == this)
                return true;
            if (o instanceof Map.Entry) {
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                if (Objects.equals(key, e.getKey()) &&
                        Objects.equals(value, e.getValue()))
                    return true;
            }
            return false;
        }
    }

    /* ---------------- Static utilities -------------- */


    /*
    默认null值hash为0
    拿到 key 的 hashCode 值
    将 hashCode 的高位参与运算，重新计算 hash 值
     */
    static final int hash(Object key) {
        int h;
        //源码喜欢在 if/for 等语句中进行赋值并判断
        return (key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16);
    }

    /**
     * Returns x's Class if it is of the form "class C implements
     * Comparable<C>", else null.
     */
    /*
     * 首先判断是否实现了Comparable接口,如果实现了则判断x是不是String类型
     * 如果是String类则返回该String.class
     * 没实现则返回null
     *
     * 在HashMap中查找通过key进行查找,而多数情况下我们都会用String来作为这个key
     * 那么在comparableClassFor中进行判断,可以跳过获得接口等一系列操作,大大优化了程序的执行效率.
     */
    static Class<?> comparableClassFor(Object x)
    {
        //判断x是否实现了Comparable接口
        if (x instanceof Comparable)
        {
            Class<?> c;
            Type[] ts, as;
            Type t;
            ParameterizedType p;
            //校验x是否为String类型
            if ((c = x.getClass()) == String.class) // bypass checks
                return c;
            if ((ts = c.getGenericInterfaces()) != null)
            {
                //遍历x实现的所有接口
                for (int i = 0; i < ts.length; ++i)
                {
                    //如果x实现了Comparable接口，则返回x的Class
                    if (((t = ts[i]) instanceof ParameterizedType) &&
                            ((p = (ParameterizedType) t).getRawType() ==
                                    Comparable.class) &&
                            (as = p.getActualTypeArguments()) != null &&
                            as.length == 1 && as[0] == c) // type arg is c
                        return c;
                }
            }
        }
        return null;
    }

    /**
     * Returns k.compareTo(x) if x matches kc (k's screened comparable
     * class), else 0.
     */
    //如果x的类型是kc，返回k.compareTo(x)的比较结果
//    一般用到comparableClassFor方法来获取该元素键的Class，然后再通过compareComparables方法来比较两个对象的大小。
    @SuppressWarnings({"rawtypes", "unchecked"}) // for cast to Comparable
    //kc（key class）为 key 的类
    static int compareComparables(Class<?> kc, Object k, Object x)
    {
        return (x == null || x.getClass() != kc ? 0 :
                ((Comparable) k).compareTo(x));
    }

    /**
     * Returns a power of two size for the given target capacity.
     */
/*
    例如10001(17)
    首先cap-1:     10000
    n |= n >>> 1: n=(10000 | 01000) =11000
    n |= n >>> 2: n=(11000 | 00110) =11110
    n |= n >>> 4: n=(11110 | 00001) =11111
    n |= n >>> 8: n=(11111 | 00000) =11111
    n |= n >>> 16: n=(11111 | 00000) =11111
    return n+1:100000(32)
    ...
    因为int为32位,所以为了保证结果,最后右移16位结束
    使得要求的数字1开始的后面全为1
 */
    //大于等于输入参数且最近的2的整数次幂的数
    //无符号右移>>>: 就是右移之后，无论该数为正还是为负，右移之后左边都是补上0
    static final int tableSizeFor(int cap)
    {
        //cap-1是为了例如16这些之后还是16
        //如果没有这一步,10000则会变成11111,最后100000(32),不符合
        int n = cap - 1;
        n |= n >>> 1;
        n |= n >>> 2;
        n |= n >>> 4;
        n |= n >>> 8;
        n |= n >>> 16;
        return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }

    /* ---------------- Fields -------------- */

    /**
     * The table, initialized on first use, and resized as
     * necessary. When allocated, length is always a power of two.
     * (We also tolerate length zero in some operations to allow
     * bootstrapping mechanics that are currently not needed.)
     */
    /*
    第一次put时初始化
    存储元素的数组，总是2的幂次倍
     */
    transient Node<K, V>[] table;

    /**
     * Holds cached entrySet(). Note that AbstractMap fields are used
     * for keySet() and values().
     */
    //遍历时经常用到的
    transient Set<Map.Entry<K, V>> entrySet;

    /**
     * The number of key-value mappings contained in this map.
     */
    // 存放元素的个数，注意这个不等于数组的长度。
    transient int size;

    /**
     * The number of times this HashMap has been structurally modified
     * Structural modifications are those that change the number of mappings in
     * the HashMap or otherwise modify its internal structure (e.g.,
     * rehash).  This field is used to make iterators on Collection-views of
     * the HashMap fail-fast.  (See ConcurrentModificationException).
     */
    // 每次扩容和更改map结构的计数器
    transient int modCount;

    /**
     * The next size value at which to resize (capacity * load factor).
     *
     * @serial
     */
    // (The javadoc description is true upon serialization.
    // Additionally, if the table array has not been allocated, this
    // field holds the initial array capacity, or zero signifying
    // DEFAULT_INITIAL_CAPACITY.)
//    threshold表示当HashMap的size大于threshold时会执行resize操作。
//    threshold=capacity*loadFactor
    int threshold;

    /**
     * The load factor for the hash table.
     *
     * @serial
     */
    final float loadFactor;

    /* ---------------- Public operations -------------- */

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and load factor.
     *
     * @param initialCapacity the initial capacity
     * @param loadFactor      the load factor
     * @throws IllegalArgumentException if the initial capacity is negative
     *                                  or the load factor is nonpositive
     */
    //开始没有赋值给capacity,而是给了threshold
    public HashMap(int initialCapacity, float loadFactor)
    {
        if (initialCapacity < 0)
            throw new IllegalArgumentException("Illegal initial capacity: " +
                    initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY)
            initialCapacity = MAXIMUM_CAPACITY;
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new IllegalArgumentException("Illegal load factor: " +
                    loadFactor);
//        此处仅用于接收初始容量大小（capacity）、加载因子(Load factor)，但仍无真正初始化哈希表，即初始化存储数组table
        //此处不是真正的阈值,该阈值后面会重新计算
        this.loadFactor = loadFactor;
        this.threshold = tableSizeFor(initialCapacity);//得到大于他的最小二次幂
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and the default load factor (0.75).
     *
     * @param initialCapacity the initial capacity.
     * @throws IllegalArgumentException if the initial capacity is negative.
     */
    public HashMap(int initialCapacity)
    {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the default initial capacity
     * (16) and the default load factor (0.75).
     */
    //这里没传入DEFAULT_CAPACITY
    public HashMap()
    {
        this.loadFactor = DEFAULT_LOAD_FACTOR; // all other fields defaulted
    }

    /**
     * Constructs a new <tt>HashMap</tt> with the same mappings as the
     * specified <tt>Map</tt>.  The <tt>HashMap</tt> is created with
     * default load factor (0.75) and an initial capacity sufficient to
     * hold the mappings in the specified <tt>Map</tt>.
     *
     * @param m the map whose mappings are to be placed in this map
     * @throws NullPointerException if the specified map is null
     */
    public HashMap(Map<? extends K, ? extends V> m)
    {
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        putMapEntries(m, false);
    }

    /**
     * Implements Map.putAll and Map constructor.
     *
     * @param m     the map
     * @param evict false when initially constructing this map, else
     *              true (relayed to method afterNodeInsertion).
     */
    //如果是构造方法,则evict为false
    final void putMapEntries(Map<? extends K, ? extends V> m, boolean evict)
    {
        int s = m.size();
        if (s > 0)
        {
            if (table == null)// 说明是拷贝构造函数来调用的putMapEntries，或者构造后还没放过任何元素
            { // pre-size
                float ft = ((float) s / loadFactor) + 1.0F;//计算出所需容量,因为之后要向下取整,所以再+1
                //始终不能超过最大容量
                int t = ((ft < (float) MAXIMUM_CAPACITY) ?
                        (int) ft : MAXIMUM_CAPACITY);
//                这里的threshold成员实际存放的值是capacity的值。
//                因为在table还没有初始化时（table还是null），用户给定的capacity会暂存到threshold成员上去
                if (t > threshold)
                    threshold = tableSizeFor(t);//大于它的最小的二次幂
            }
            else if (s > threshold)
                resize();//说明原本有,但是原本的位置不够了
            //循环里的putVal可能也会触发resize
            for (Map.Entry<? extends K, ? extends V> e : m.entrySet())
            {
                K key = e.getKey();
                V value = e.getValue();
                putVal(hash(key), key, value, false, evict);
            }
        }
    }

    /**
     * Returns the number of key-value mappings in this map.
     *
     * @return the number of key-value mappings in this map
     */
    public int size()
    {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this map contains no key-value mappings.
     *
     * @return <tt>true</tt> if this map contains no key-value mappings
     */
    public boolean isEmpty()
    {
        return size == 0;
    }


    //key为null也可能是本身就是存储null的key
    public V get(Object key)
    {
        Node<K, V> e;
        return (e = getNode(hash(key), key)) == null ? null : e.value;
    }

    /**
     * Implements Map.get and related methods.
     *
     * @param hash hash for key
     * @param key  the key
     * @return the node, or null if none
     */
    final Node<K, V> getNode(int hash, Object key)
    {
        Node<K, V>[] tab;
        Node<K, V> first, e;
        int n;
        K k;
        //table不为空,table长度不为0,table相应的索引位置不为空
        if ((tab = table) != null && (n = tab.length) > 0 &&
                (first = tab[(n - 1) & hash]) != null)
        {
            //因为索引相同hash却不一定相同(多个hash映射到同一个槽)
            //hash相同并不一定是键相同,还要检查键是否相同或相等
            if (first.hash == hash && // always check first node
                    ((k = first.key) == key || (key != null && key.equals(k))))
                return first;
            if ((e = first.next) != null)
            {
                //如果是红黑树节点，则调用红黑树的查找目标节点方法getTreeNode
                if (first instanceof TreeNode)
                    return ((TreeNode<K, V>) first).getTreeNode(hash, key);
                do
                {
                    //执行链表节点的查找，向下遍历链表, 直至找到节点的key和入参的key相等时,返回该节点
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                        return e;
                } while ((e = e.next) != null);
            }
        }
        return null;
    }

    /**
     * Returns <tt>true</tt> if this map contains a mapping for the
     * specified key.
     *
     * @param key The key whose presence in this map is to be tested
     * @return <tt>true</tt> if this map contains a mapping for the specified
     * key.
     */
    public boolean containsKey(Object key)
    {
        return getNode(hash(key), key) != null;
    }

    /*
    put相同键会替代
    返回被替换的那个key的value或者null
     */
    public V put(K key, V value)
    {
        return putVal(hash(key), key, value, false, true);
    }


    /*
    onlyIfAbsent 当键相同时,不修改已存在的值
    evict        仅在创建时为false
    返回值 先前的值或null
     */
    final V putVal(int hash, K key, V value, boolean onlyIfAbsent,
                   boolean evict)
    {
        Node<K, V>[] tab;
        Node<K, V> p;//当前节点
        int n, i;
//        校验table是否为空或者length等于0，如果是则调用resize方法进行初始化
        if ((tab = table) == null || (n = tab.length) == 0)
            n = (tab = resize()).length;
        //直接新建节点,多好
        if ((p = tab[i = (n - 1) & hash]) == null)
            tab[i] = newNode(hash, key, value, null);
        else
        {
            Node<K, V> e;
            K k;
            //直接覆盖相同的值p
            if (p.hash == hash &&
                    ((k = p.key) == key || (key != null && key.equals(k))))
                e = p;
                //调用红黑树的put方法
            else if (p instanceof TreeNode)
                e = ((TreeNode<K, V>) p).putTreeVal(this, tab, hash, key, value);
            else
            {
                //binCount记录是否需要树化
                for (int binCount = 0; ; ++binCount)
                {
                    //1.8采用了尾插法
                    if ((e = p.next) == null)
                    {
                        p.next = newNode(hash, key, value, null);
                        // 校验节点数是否超过TREEIFY_THRESHOLD，如果超过则调用treeifyBin方法将链表节点转为红黑树节点，
                        // 减一是因为前面加了节点,但是binCount没更新
                        if (binCount >= TREEIFY_THRESHOLD - 1) // -1 for 1st
                            treeifyBin(tab, hash);
                        break;//此时break,e==null,不会进入 if (e != null)
                    }
                    //说明存在相同的key,要修改
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                        break;
                    p = e;
                    //继续遍历下一个Node
                }
            }
            //代表目标节点存在，使用传入的value覆盖该节点的value，并返回oldValue
            if (e != null)
            {
                //说明要放的位置之前存在了元素
                V oldValue = e.value;
                if (!onlyIfAbsent || oldValue == null)
                    e.value = value;
                afterNodeAccess(e);// 用于LinkedHashMap
                return oldValue;
            }
        }
        ++modCount;
        //插入则size+1,而且大于threshold则需要扩容了
        if (++size > threshold)
            resize();
        // 用于LinkedHashMap的钩子函数
        afterNodeInsertion(evict);
        return null;
    }

    /**
     * Initializes or doubles table size.  If null, allocates in
     * accord with initial capacity target held in field threshold.
     * Otherwise, because we are using power-of-two expansion, the
     * elements from each bin must either stay at same index, or move
     * with a power of two offset in the new table.
     *
     * @return the table
     */
    /*
    初始化或扩容
     */
    final Node<K, V>[] resize()
    {
        Node<K, V>[] oldTab = table;
        int oldCap = (oldTab == null) ? 0 : oldTab.length;
        int oldThr = threshold;
        int newCap, newThr = 0;

        //扩容前的table不为空,即正常的扩容操作.将容量变成原来的两倍
        if (oldCap > 0)
        {
            if (oldCap >= MAXIMUM_CAPACITY)
            {
                //阈值设为最大,但是不扩容
                threshold = Integer.MAX_VALUE;
                return oldTab;
            }
            else if ((newCap = oldCap << 1) < MAXIMUM_CAPACITY &&
                    oldCap >= DEFAULT_INITIAL_CAPACITY)
                newThr = oldThr << 1; // double threshold
            //容量和阈值都*2扩容
        }
        //如果老表的容量为0, 老表的阈值大于0, 是因为初始容量被放入阈值，则将新表的容量设置为老表的阈值
        //对应前两种初始化HashMap的方法 例如new HashMap<>(32)
        else if (oldThr > 0) // initial capacity was placed in threshold
            newCap = oldThr;
        else
        {
            //老表的容量为0, 老表的阈值为0，这种情况是没有传初始容量的new方法创建的空表，将阈值和容量设置为默认值
            //即初始化的第三种情况 new HashMap()
            // zero initial threshold signifies using defaults
            newCap = DEFAULT_INITIAL_CAPACITY;
            newThr = (int) (DEFAULT_LOAD_FACTOR * DEFAULT_INITIAL_CAPACITY);
        }

        //对应前两种初始化方法,之前的threshold已经在初始化newCap时用过了
        if (newThr == 0)//计算新的负载因子
        {
            //很合理,假如new HashMap(32),即ft=32*0.75
            float ft = (float) newCap * loadFactor;
            newThr = (newCap < MAXIMUM_CAPACITY && ft < (float) MAXIMUM_CAPACITY ?
                    (int) ft : Integer.MAX_VALUE);
        }
        threshold = newThr;
        //说明在第一次调用resize()方法时才进行了tab的初始化
        @SuppressWarnings({"rawtypes", "unchecked"})
        Node<K, V>[] newTab = (Node<K, V>[]) new Node[newCap];
        table = newTab;
        //如果老表不为空，则需遍历所有节点，将节点赋值给新表
        if (oldTab != null)
        {
            for (int j = 0; j < oldCap; ++j)
            {
                Node<K, V> e;
                if ((e = oldTab[j]) != null)// 将索引值为j的老表头节点赋值给e
                {
                    oldTab[j] = null;// 将老表的节点设置为空, 以便垃圾收集器回收空间
                    if (e.next == null)//只有一个节点,直接散列
                        newTab[e.hash & (newCap - 1)] = e;
                    else if (e instanceof TreeNode)//调用红黑树的重新散列
                        ((TreeNode<K, V>) e).split(this, newTab, j, oldCap);
                    else
                    { // preserve order
                        Node<K, V> loHead = null, loTail = null;
                        Node<K, V> hiHead = null, hiTail = null;
                        Node<K, V> next;
                        do
                        {
                            next = e.next;
                            /*
                            例如 3和19,00011,10011
                            如果oldCap=10000(16)
                            00011 & 10000 = 0
                            10011 & 10000 = 10000 != 0
                            将原本在一个索引的分成两条链表
                             */
                            //因为扩容为原来两倍,所以根据oldCap的最高位,来把链表区分成两块链表
                            //如果 e 的 hash 值与老表的容量进行位与运算为 0，则说明 e 节点扩容后的索引位置跟老表的索引位置一样
                            if ((e.hash & oldCap) == 0)
                            {
                                //好强的代码,巧妙的构造了链表
                                //还是尾插法,尾插法就要维护一个头部(loHead),以及当前指针(loTail)
                                if (loTail == null)
                                    loHead = e;
                                else
                                    loTail.next = e;
                                loTail = e;
                            }
                            else
                            {
                                if (hiTail == null)
                                    hiHead = e;
                                else
                                    hiTail.next = e;
                                hiTail = e;
                            }
                        } while ((e = next) != null);//散列开来
                        if (loTail != null)
                        {
                            loTail.next = null;
                            newTab[j] = loHead;
                        }
                        if (hiTail != null)
                        {
                            hiTail.next = null;
                            newTab[j + oldCap] = hiHead;//放在新的位置
                        }
                    }
                }
            }
        }
        return newTab;
    }

    /**
     * Replaces all linked nodes in bin at index for given hash unless
     * table is too small, in which case resizes instead.
     */
    //转为红黑树节点后，链表的结构还存在，通过 next 属性维持，红黑树节点在进行操作时都会维护链表的结构
//    在红黑树上，叶子节点也可能有 next 节点，因为红黑树的结构跟链表的结构是互不影响的
    final void treeifyBin(Node<K, V>[] tab, int hash)
    {
        int n, index;
        Node<K, V> e;
        //如果table为空或者table的长度小于64, 调用resize方法进行扩容
        if (tab == null || (n = tab.length) < MIN_TREEIFY_CAPACITY)
            resize();
        else if ((e = tab[index = (n - 1) & hash]) != null)
        {
            TreeNode<K, V> hd = null, tl = null;
            //这一步只是构造了一个双向链表
            do
            {
                //将链表节点转红黑树节点,但是没有构建成树
                TreeNode<K, V> p = replacementTreeNode(e, null);
                //第一次循环将头节点赋值给hd
                if (tl == null)
                    hd = p;
                else
                {
                    p.prev = tl;//循环只是赋值给了prev,还没构建红黑树
                    tl.next = p;
                }
                tl = p;
            } while ((e = e.next) != null);

            //将table该索引位置赋值为新转的TreeNode的头节点，如果该节点不为空，则以以头节点(hd)为根节点, 构建红黑树
            if ((tab[index] = hd) != null)
                hd.treeify(tab);
        }
    }

    /**
     * Copies all of the mappings from the specified map to this map.
     * These mappings will replace any mappings that this map had for
     * any of the keys currently in the specified map.
     *
     * @param m mappings to be stored in this map
     * @throws NullPointerException if the specified map is null
     */
    public void putAll(Map<? extends K, ? extends V> m)
    {
        putMapEntries(m, true);
    }


    //返回null可能本来就绑定了null,也可能是找不到key
    public V remove(Object key)
    {
        Node<K, V> e;
        return (e = removeNode(hash(key), key, null, false, true)) == null ?
                null : e.value;
    }

    /**
     * Implements Map.remove and related methods.
     *
     * @param hash       hash for key
     * @param key        the key
     * @param value      the value to match if matchValue, else ignored
     * @param matchValue if true only remove if value is equal
     * @param movable    if false do not move other nodes while removing
     * @return the node, or null if none
     */
    final Node<K, V> removeNode(int hash, Object key, Object value,
                                boolean matchValue, boolean movable)
    {
        Node<K, V>[] tab;
        Node<K, V> p;
        int n, index;
        if ((tab = table) != null && (n = tab.length) > 0 &&
                (p = tab[index = (n - 1) & hash]) != null)
        {
            Node<K, V> node = null, e;
            K k;
            V v;
            //找到要删除的那个节点
            if (p.hash == hash &&
                    ((k = p.key) == key || (key != null && key.equals(k))))
                node = p;
            else if ((e = p.next) != null)
            {
                if (p instanceof TreeNode)
                    node = ((TreeNode<K, V>) p).getTreeNode(hash, key);
                else
                {
                    do
                    {
                        if (e.hash == hash &&
                                ((k = e.key) == key ||
                                        (key != null && key.equals(k))))
                        {
                            node = e;
                            break;
                        }
                        p = e;
                    } while ((e = e.next) != null);
                }
            }
            //是否需要值相同才删除
            if (node != null && (!matchValue || (v = node.value) == value ||
                    (value != null && value.equals(v))))
            {
                if (node instanceof TreeNode)
                    ((TreeNode<K, V>) node).removeTreeNode(this, tab, movable);
                else if (node == p)//说明删除的是头元素
                    tab[index] = node.next;
                else //p是要删除元素的前一个元素(对应上面的else if)
                    p.next = node.next;
                ++modCount;
                --size;
                afterNodeRemoval(node);//删除后的钩子方法
                return node;
            }
        }
        return null;
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    public void clear()
    {
        Node<K, V>[] tab;
        modCount++;
        if ((tab = table) != null && size > 0)
        {
            size = 0;
            for (int i = 0; i < tab.length; ++i)
                tab[i] = null;
        }
    }

    //containsValue代价真的高,全部表中寻找
    public boolean containsValue(Object value)
    {
        Node<K, V>[] tab;
        V v;
        if ((tab = table) != null && size > 0)
        {
            for (int i = 0; i < tab.length; ++i)
            {
                for (Node<K, V> e = tab[i]; e != null; e = e.next)
                {
                    if ((v = e.value) == value ||
                            (value != null && value.equals(v)))
                        return true;
                }
            }
        }
        return false;
    }


    public Set<K> keySet()
    {
        Set<K> ks = keySet;
        if (ks == null)
        {
            ks = new KeySet();
            keySet = ks;
        }
        return ks;
    }

    final class KeySet extends AbstractSet<K>
    {
        public final int size()
        {
            return size;
        }

        public final void clear()
        {
            this.clear();
        }

        public final Iterator<K> iterator()
        {
            return new KeyIterator();
        }

        public final boolean contains(Object o)
        {
            return containsKey(o);
        }

        public final boolean remove(Object key)
        {
            return removeNode(hash(key), key, null, false, true) != null;
        }

        public final Spliterator<K> spliterator()
        {
            return new KeySpliterator<>(this, 0, -1, 0, 0);
        }

        public final void forEach(Consumer<? super K> action)
        {
            Node<K, V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null)
            {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i)
                {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.key);
                }
                //fail-fast机制
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    public Collection<V> values()
    {
        Collection<V> vs = values;
        if (vs == null)
        {
            vs = new Values();
            values = vs;
        }
        return vs;
    }

    final class Values extends AbstractCollection<V>
    {
        public final int size()
        {
            return size;
        }

        public final void clear()
        {
            this.clear();
        }

        public final Iterator<V> iterator()
        {
            return new ValueIterator();
        }

        public final boolean contains(Object o)
        {
            return containsValue(o);
        }

        public final Spliterator<V> spliterator()
        {
            return new ValueSpliterator<>(this, 0, -1, 0, 0);
        }

        public final void forEach(Consumer<? super V> action)
        {
            Node<K, V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null)
            {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i)
                {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.value);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }


    public Set<Map.Entry<K, V>> entrySet()
    {
        Set<Map.Entry<K, V>> es;
        return (es = entrySet) == null ? (entrySet = new EntrySet()) : es;
    }

    final class EntrySet extends AbstractSet<Map.Entry<K, V>>
    {
        public final int size()
        {
            return size;
        }

        public final void clear()
        {
            this.clear();
        }

        public final Iterator<Map.Entry<K, V>> iterator()
        {
            return new EntryIterator();
        }

        public final boolean contains(Object o)
        {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            Object key = e.getKey();
            Node<K, V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }

        public final boolean remove(Object o)
        {
            if (o instanceof Map.Entry)
            {
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }

        public final Spliterator<Map.Entry<K, V>> spliterator()
        {
            return new EntrySpliterator<>(this, 0, -1, 0, 0);
        }

        public final void forEach(Consumer<? super Map.Entry<K, V>> action)
        {
            Node<K, V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null)
            {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i)
                {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next)
                        action.accept(e);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    // Overrides of JDK8 Map extension methods

    //原来在这里
    @Override
    public V getOrDefault(Object key, V defaultValue)
    {
        Node<K, V> e;
        return (e = getNode(hash(key), key)) == null ? defaultValue : e.value;
    }

    @Override
    public V putIfAbsent(K key, V value)
    {
        return putVal(hash(key), key, value, true, true);
    }

    @Override
    public boolean remove(Object key, Object value)
    {
        return removeNode(hash(key), key, value, true, true) != null;
    }

    //key,value都相同,才放入
    @Override
    public boolean replace(K key, V oldValue, V newValue)
    {
        Node<K, V> e;
        V v;
        if ((e = getNode(hash(key), key)) != null &&
                ((v = e.value) == oldValue || (v != null && v.equals(oldValue))))
        {
            e.value = newValue;
            afterNodeAccess(e);
            return true;
        }
        return false;
    }

    @Override
    public V replace(K key, V value)
    {
        Node<K, V> e;
        if ((e = getNode(hash(key), key)) != null)
        {
            V oldValue = e.value;
            e.value = value;
            afterNodeAccess(e);
            return oldValue;
        }
        return null;
    }

    //对 hashMap 中指定 key 的值进行重新计算，如果不存在这个 key，则添加到 hasMap 中
    @Override
    public V computeIfAbsent(K key,
                             Function<? super K, ? extends V> mappingFunction)
    {
        if (mappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K, V>[] tab;
        Node<K, V> first;
        int n, i;
        int binCount = 0;
        TreeNode<K, V> t = null;
        Node<K, V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null)
        {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K, V>) first).getTreeNode(hash, key);
            else
            {
                Node<K, V> e = first;
                K k;
                do
                {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                    {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
            V oldValue;
            if (old != null && (oldValue = old.value) != null)
            {
                afterNodeAccess(old);
                return oldValue;
            }
        }
        V v = mappingFunction.apply(key);
        if (v == null)
        {
            return null;
        }
        else if (old != null)
        {
            old.value = v;
            afterNodeAccess(old);
            return v;
        }
        else if (t != null)
            t.putTreeVal(this, tab, hash, key, v);
        else
        {
            tab[i] = newNode(hash, key, v, first);
            if (binCount >= TREEIFY_THRESHOLD - 1)
                treeifyBin(tab, hash);
        }
        ++modCount;
        ++size;
        afterNodeInsertion(true);
        return v;
    }

    public V computeIfPresent(K key,
                              BiFunction<? super K, ? super V, ? extends V> remappingFunction)
    {
        if (remappingFunction == null)
            throw new NullPointerException();
        Node<K, V> e;
        V oldValue;
        int hash = hash(key);
        if ((e = getNode(hash, key)) != null &&
                (oldValue = e.value) != null)
        {
            V v = remappingFunction.apply(key, oldValue);
            if (v != null)
            {
                e.value = v;
                afterNodeAccess(e);
                return v;
            }
            else
                removeNode(hash, key, null, false, true);
        }
        return null;
    }

    @Override
    public V compute(K key,
                     BiFunction<? super K, ? super V, ? extends V> remappingFunction)
    {
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K, V>[] tab;
        Node<K, V> first;
        int n, i;
        int binCount = 0;
        TreeNode<K, V> t = null;
        Node<K, V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null)
        {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K, V>) first).getTreeNode(hash, key);
            else
            {
                Node<K, V> e = first;
                K k;
                do
                {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                    {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        V oldValue = (old == null) ? null : old.value;
        V v = remappingFunction.apply(key, oldValue);
        if (old != null)
        {
            if (v != null)
            {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
        }
        else if (v != null)
        {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, v);
            else
            {
                tab[i] = newNode(hash, key, v, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return v;
    }

    @Override
    public V merge(K key, V value,
                   BiFunction<? super V, ? super V, ? extends V> remappingFunction)
    {
        if (value == null)
            throw new NullPointerException();
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K, V>[] tab;
        Node<K, V> first;
        int n, i;
        int binCount = 0;
        TreeNode<K, V> t = null;
        Node<K, V> old = null;
        if (size > threshold || (tab = table) == null ||
                (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null)
        {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K, V>) first).getTreeNode(hash, key);
            else
            {
                Node<K, V> e = first;
                K k;
                do
                {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                    {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        if (old != null)
        {
            V v;
            if (old.value != null)
                v = remappingFunction.apply(old.value, value);
            else
                v = value;
            if (v != null)
            {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
            return v;
        }
        if (value != null)
        {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, value);
            else
            {
                tab[i] = newNode(hash, key, value, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return value;
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action)
    {
        Node<K, V>[] tab;
        if (action == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null)
        {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i)
            {
                for (Node<K, V> e = tab[i]; e != null; e = e.next)
                    action.accept(e.key, e.value);
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function)
    {
        Node<K, V>[] tab;
        if (function == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null)
        {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i)
            {
                for (Node<K, V> e = tab[i]; e != null; e = e.next)
                {
                    e.value = function.apply(e.key, e.value);
                }
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    /* ------------------------------------------------------------ */
    // Cloning and serialization

//键和值不会被深拷贝
    @SuppressWarnings("unchecked")
    @Override
    public Object clone()
    {
        HashMap<K, V> result;
        try
        {
            result = (HashMap<K, V>) super.clone();
            /*
                AbstractMap<?,?> result = (AbstractMap<?,?>)super.clone();
                result.keySet = null;
                result.values = null;
                return result;
             */
        }
        catch (CloneNotSupportedException e)
        {
            // this shouldn't happen, since we are Cloneable
            throw new InternalError(e);
        }
        result.reinitialize();//全部初始化为0
        //因为本质上就是调用put方法批量加入,put方法也只是改了个引用罢了
        result.putMapEntries(this, false);
        return result;
    }

    // These methods are also used when serializing HashSets
    final float loadFactor()
    {
        return loadFactor;
    }

    //说明一开始你随便初始化一个,都会有容量,尽管可能都没创建出来
    //额,包访问权限,无语
    final int capacity()
    {
        return (table != null) ? table.length :
                (threshold > 0) ? threshold :
                        DEFAULT_INITIAL_CAPACITY;
    }

    //序列化操作
    private void writeObject(java.io.ObjectOutputStream s)
            throws IOException
    {
        int buckets = capacity();
        // Write out the threshold, loadfactor, and any hidden stuff
        s.defaultWriteObject();
        s.writeInt(buckets);
        s.writeInt(size);
        internalWriteEntries(s);
    }

    //序列化操作
    private void readObject(java.io.ObjectInputStream s)
            throws IOException, ClassNotFoundException
    {
        // Read in the threshold (ignored), loadfactor, and any hidden stuff
        s.defaultReadObject();
        reinitialize();
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new InvalidObjectException("Illegal load factor: " +
                    loadFactor);
        s.readInt();                // Read and ignore number of buckets
        int mappings = s.readInt(); // Read number of mappings (size)
        if (mappings < 0)
            throw new InvalidObjectException("Illegal mappings count: " +
                    mappings);
        else if (mappings > 0)
        { // (if zero, use defaults)
            // Size the table using given load factor only if within
            // range of 0.25...4.0
            float lf = Math.min(Math.max(0.25f, loadFactor), 4.0f);
            float fc = (float) mappings / lf + 1.0f;
            int cap = ((fc < DEFAULT_INITIAL_CAPACITY) ?
                    DEFAULT_INITIAL_CAPACITY :
                    (fc >= MAXIMUM_CAPACITY) ?
                            MAXIMUM_CAPACITY :
                            tableSizeFor((int) fc));
            float ft = (float) cap * lf;
            threshold = ((cap < MAXIMUM_CAPACITY && ft < MAXIMUM_CAPACITY) ?
                    (int) ft : Integer.MAX_VALUE);

            // Check Map.Entry[].class since it's the nearest public type to
            // what we're actually creating.
            SharedSecrets.getJavaOISAccess().checkArray(s, Map.Entry[].class, cap);
            @SuppressWarnings({"rawtypes", "unchecked"})
            Node<K, V>[] tab = (Node<K, V>[]) new Node[cap];
            table = tab;

            // Read the keys and values, and put the mappings in the HashMap
            for (int i = 0; i < mappings; i++)
            {
                @SuppressWarnings("unchecked")
                K key = (K) s.readObject();
                @SuppressWarnings("unchecked")
                V value = (V) s.readObject();
                putVal(hash(key), key, value, false, false);
            }
        }
    }

    /* ------------------------------------------------------------ */
    // iterators
    /*开始迭代器next就指向第一个非空元素了,而current=null,所以此时不能remove
    每次调用nextNode时,返回该元素,并且next指向下一个元素,而且current也等于当前元素,所以可以删除
    而hasNext直接判断next是否为空即可
    (终于明白最开始看 java核心技术时讲的东西了
    * */
    abstract class HashIterator
    {
        Node<K, V> next;        // next entry to return
        Node<K, V> current;     // current entry
        int expectedModCount;  // for fast-fail
        int index;             // current slot

        HashIterator()
        {
            expectedModCount = modCount;
            Node<K, V>[] t = table;
            current = next = null;
            index = 0;
            if (t != null && size > 0)
            { // advance to first entry
                do
                {
                } while (index < t.length && (next = t[index++]) == null);
                //让next能指向第一个非空的元素
            }
        }

        public final boolean hasNext()
        {
            return next != null;
        }

        final Node<K, V> nextNode()
        {
            Node<K, V>[] t;
            Node<K, V> e = next;
            if (modCount != expectedModCount)//fail-fast机制
                throw new ConcurrentModificationException();
            if (e == null)
                throw new NoSuchElementException();
            //找到下一个非空元素
            if ((next = (current = e).next) == null && (t = table) != null)
            {
                do
                {
                } while (index < t.length && (next = t[index++]) == null);
            }
            return e;
        }

        public final void remove()
        {
            Node<K, V> p = current;
            if (p == null)
                throw new IllegalStateException();
            //依然是fail-fast
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            current = null;
            K key = p.key;
            //这里导致的modCount+1,所以需要下一条语句
            removeNode(hash(key), key, null, false, false);
            expectedModCount = modCount;//此处remove不会触发fail-fast
        }
    }

    final class KeyIterator extends HashIterator
            implements Iterator<K>
    {
        public final K next()
        {
            return nextNode().key;
        }
    }

    final class ValueIterator extends HashIterator
            implements Iterator<V>
    {
        public final V next()
        {
            return nextNode().value;
        }
    }

    final class EntryIterator extends HashIterator
            implements Iterator<Map.Entry<K, V>>
    {
        public final Map.Entry<K, V> next()
        {
            return nextNode();
        }
    }

    /* ------------------------------------------------------------ */
    // spliterators
    //为了并行计算的需要
    static class HashMapSpliterator<K, V>
    {
        final HashMap<K, V> map;
        Node<K, V> current;          // current node
        int index;                  // current index, modified on advance/split
        int fence;                  // one past last index
        int est;                    // size estimate
        int expectedModCount;       // for comodification checks

        HashMapSpliterator(HashMap<K, V> m, int origin,
                           int fence, int est,
                           int expectedModCount)
        {
            this.map = m;
            this.index = origin;
            this.fence = fence;
            this.est = est;
            this.expectedModCount = expectedModCount;
        }

        final int getFence()
        { // initialize fence and size on first use
            int hi;
            if ((hi = fence) < 0)
            {
                HashMap<K, V> m = map;
                est = m.size;
                expectedModCount = m.modCount;
                Node<K, V>[] tab = m.table;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            return hi;
        }

        public final long estimateSize()
        {
            getFence(); // force init
            return (long) est;
        }
    }

    static final class KeySpliterator<K, V>
            extends HashMapSpliterator<K, V>
            implements Spliterator<K>
    {
        KeySpliterator(HashMap<K, V> m, int origin, int fence, int est,
                       int expectedModCount)
        {
            super(m, origin, fence, est, expectedModCount);
        }

        public KeySpliterator<K, V> trySplit()
        {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new KeySpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super K> action)
        {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K, V> m = map;
            Node<K, V>[] tab = m.table;
            if ((hi = fence) < 0)
            {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null))
            {
                Node<K, V> p = current;
                current = null;
                do
                {
                    if (p == null)
                        p = tab[i++];
                    else
                    {
                        action.accept(p.key);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super K> action)
        {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K, V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0)
            {
                while (current != null || index < hi)
                {
                    if (current == null)
                        current = tab[index++];
                    else
                    {
                        K k = current.key;
                        current = current.next;
                        action.accept(k);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics()
        {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                    Spliterator.DISTINCT;
        }
    }

    static final class ValueSpliterator<K, V>
            extends HashMapSpliterator<K, V>
            implements Spliterator<V>
    {
        ValueSpliterator(HashMap<K, V> m, int origin, int fence, int est,
                         int expectedModCount)
        {
            super(m, origin, fence, est, expectedModCount);
        }

        public ValueSpliterator<K, V> trySplit()
        {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new ValueSpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super V> action)
        {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K, V> m = map;
            Node<K, V>[] tab = m.table;
            if ((hi = fence) < 0)
            {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null))
            {
                Node<K, V> p = current;
                current = null;
                do
                {
                    if (p == null)
                        p = tab[i++];
                    else
                    {
                        action.accept(p.value);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super V> action)
        {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K, V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0)
            {
                while (current != null || index < hi)
                {
                    if (current == null)
                        current = tab[index++];
                    else
                    {
                        V v = current.value;
                        current = current.next;
                        action.accept(v);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics()
        {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0);
        }
    }

    static final class EntrySpliterator<K, V>
            extends HashMapSpliterator<K, V>
            implements Spliterator<Map.Entry<K, V>>
    {
        EntrySpliterator(HashMap<K, V> m, int origin, int fence, int est,
                         int expectedModCount)
        {
            super(m, origin, fence, est, expectedModCount);
        }

        public EntrySpliterator<K, V> trySplit()
        {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super Map.Entry<K, V>> action)
        {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K, V> m = map;
            Node<K, V>[] tab = m.table;
            if ((hi = fence) < 0)
            {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null))
            {
                Node<K, V> p = current;
                current = null;
                do
                {
                    if (p == null)
                        p = tab[i++];
                    else
                    {
                        action.accept(p);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super Map.Entry<K, V>> action)
        {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K, V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0)
            {
                while (current != null || index < hi)
                {
                    if (current == null)
                        current = tab[index++];
                    else
                    {
                        Node<K, V> e = current;
                        current = current.next;
                        action.accept(e);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics()
        {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                    Spliterator.DISTINCT;
        }
    }

    /* ------------------------------------------------------------ */
    // LinkedHashMap support


    /*
     * The following package-protected methods are designed to be
     * overridden by LinkedHashMap, but not by any other subclass.
     * Nearly all other internal methods are also package-protected
     * but are declared final, so can be used by LinkedHashMap, view
     * classes, and HashSet.
     */

    // Create a regular (non-tree) node
    Node<K, V> newNode(int hash, K key, V value, Node<K, V> next)
    {
        return new Node<>(hash, key, value, next);
    }

    // For conversion from TreeNodes to plain nodes
    Node<K, V> replacementNode(Node<K, V> p, Node<K, V> next)
    {
        return new Node<>(p.hash, p.key, p.value, next);
    }

    // Create a tree bin node
    TreeNode<K, V> newTreeNode(int hash, K key, V value, Node<K, V> next)
    {
        return new TreeNode<>(hash, key, value, next);
    }

    // For treeifyBin
    TreeNode<K, V> replacementTreeNode(Node<K, V> p, Node<K, V> next)
    {
        return new TreeNode<>(p.hash, p.key, p.value, next);
    }

    /**
     * Reset to initial default state.  Called by clone and readObject.
     */
    void reinitialize()
    {
        table = null;
        entrySet = null;
        keySet = null;
        values = null;
        modCount = 0;
        threshold = 0;
        size = 0;
    }

    // Callbacks to allow LinkedHashMap post-actions 钩子函数
    void afterNodeAccess(Node<K, V> p)
    {
    }

    void afterNodeInsertion(boolean evict)
    {
    }

    void afterNodeRemoval(Node<K, V> p)
    {
    }

    // Called only from writeObject, to ensure compatible ordering.
    void internalWriteEntries(java.io.ObjectOutputStream s) throws IOException
    {
        Node<K, V>[] tab;
        if (size > 0 && (tab = table) != null)
        {
            for (int i = 0; i < tab.length; ++i)
            {
                for (Node<K, V> e = tab[i]; e != null; e = e.next)
                {
                    s.writeObject(e.key);
                    s.writeObject(e.value);
                }
            }
        }
    }

    /* ------------------------------------------------------------ */
    // Tree bins

    /**
     * Entry for Tree bins. Extends LinkedHashMap.Entry (which in turn
     * extends Node) so can be used as extension of either regular or
     * linked node.
     */
    //它继承自 LinkedHashMap.Entry ，而 LinkedHashMap.Entry 继承自 HashMap.Node ，因此还有额外的 6 个属性：
    static final class TreeNode<K, V> extends LinkedHashMap.Entry<K, V>
    {
        TreeNode<K, V> parent;  // red-black tree links
        TreeNode<K, V> left;
        TreeNode<K, V> right;
        TreeNode<K, V> prev;    // needed to unlink next upon deletion
        boolean red;//红黑树,啦啦啦

        TreeNode(int hash, K key, V val, Node<K, V> next)
        {
            super(hash, key, val, next);
        }

        /**
         * Returns root of tree containing this node.
         */
        final TreeNode<K, V> root()
        {
            for (TreeNode<K, V> r = this, p; ; )
            {
                if ((p = r.parent) == null)
                    return r;
                r = p;
            }
        }

        /**
         * Ensures that the given root is the first node of its bin.
         */
        //确保给定的根是其容器的第一个节点。
        static <K, V> void moveRootToFront(Node<K, V>[] tab, TreeNode<K, V> root)
        {
            int n;
            //1,红黑树根节点不能为空，table数组不能为空
            if (root != null && tab != null && (n = tab.length) > 0)
            {
                //2,获取红黑树根节点的应该放入的下标位置
                int index = (n - 1) & root.hash;
                TreeNode<K, V> first = (TreeNode<K, V>) tab[index];
                //3,如果当前的下标位置放得对象与需要验证的对象，不是同一个对象
                if (root != first)
                {
                    Node<K, V> rn;
                    //3.1,设置红黑树根节点的值为改下标位置的值
                    tab[index] = root;
                    TreeNode<K, V> rp = root.prev;
                    //3.2,重置红黑树根节点的上下级关系，主要是调整root,root.prev,root.next,first;四者的关系
                    if ((rn = root.next) != null)
                        ((TreeNode<K, V>) rn).prev = rp;
                    if (rp != null)
                        rp.next = rn;
                    if (first != null)
                        first.prev = root;
                    root.next = first;
                    root.prev = null;
                }
                assert checkInvariants(root);
            }
        }

        /**
         * Finds the node starting at root p with the given hash and key.
         * The kc argument caches comparableClassFor(key) upon first use
         * comparing keys.
         */

        /**
         * 从调用此方法的节点开始查找, 通过hash值和key找到对应的节点
         * 此方法是红黑树节点的查找, 红黑树是特殊的自平衡二叉查找树
         * 平衡二叉查找树的特点：左节点<根节点<右节点
         */
        final TreeNode<K, V> find(int h, Object k, Class<?> kc)
        {
            // 1.将p节点赋值为调用此方法的节点，即为红黑树根节点
            TreeNode<K, V> p = this;

            // 2.从p节点开始向下遍历
            do
            {
                int ph, dir;
                K pk;
                TreeNode<K, V> pl = p.left, pr = p.right, q;
                // 3.如果传入的hash值小于p节点的hash值，则往p节点的左边遍历
                if ((ph = p.hash) > h)
                    p = pl;
                else if (ph < h)
                    p = pr;
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))// 5.如果传入的hash值和key值等于p节点的hash值和key值,则p节点为目标节点,返回p节点
                    return p;
                else if (pl == null) // 6.p节点的左节点为空则将向右遍历
                    p = pr;
                else if (pr == null)
                    p = pl;
                // 8.将p节点与k进行比较
                else if ((kc != null ||
                        (kc = comparableClassFor(k)) != null) &&// 8.1 kc不为空代表k实现了Comparable
                        (dir = compareComparables(kc, k, pk)) != 0)// 8.2 k<pk则dir<0, k>pk则dir>0
                    p = (dir < 0) ? pl : pr;
                    // 9.代码走到此处, 代表key所属类没有实现Comparable, 直接指定向p的右边遍历
                else if ((q = pr.find(h, k, kc)) != null)
                    return q;
                    // 10.代码走到此处代表“pr.find(h, k, kc)”为空, 因此直接向左遍历
                else
                    p = pl;
            } while (p != null);
            return null;
        }

        /**
         * Calls find for root node.
         */
        final TreeNode<K, V> getTreeNode(int h, Object k)
        {
            // 1.首先找到红黑树的根节点；2.使用根节点调用find方法
            return ((parent != null) ? root() : this).find(h, k, null);
        }

        /**
         * Tie-breaking utility for ordering insertions when equal
         * hashCodes and non-comparable. We don't require a total
         * order, just a consistent insertion rule to maintain
         * equivalence across rebalancings. Tie-breaking further than
         * necessary simplifies testing a bit.
         */
        // 用于没有实现Comparable或者hashCode相同时进行比较的方法, 只是一个一致的插入规则，用来维护重定位的等价性。
        //定义一套规则用于极端情况下比较两个参数的大小。
        static int tieBreakOrder(Object a, Object b)
        {
            int d;
            if (a == null || b == null ||
                    (d = a.getClass().getName().
                            compareTo(b.getClass().getName())) == 0)
                d = (System.identityHashCode(a) <= System.identityHashCode(b) ?
                        -1 : 1);
            return d;
        }

        /**
         * Forms tree of the nodes linked from this node.
         */
        //构建红黑树
        final void treeify(Node<K, V>[] tab)
        {
            TreeNode<K, V> root = null;
            // 1.将调用此方法的节点赋值给x，以x作为起点，开始进行遍历
            for (TreeNode<K, V> x = this, next; x != null; x = next)
            {
                next = (TreeNode<K, V>) x.next; // next赋值为x的下个节点
                x.left = x.right = null; // 将x的左右节点设置为空
                if (root == null)
                {
                    x.parent = null;
                    x.red = false;
                    root = x;
                }
                else
                {
                    K k = x.key;
                    int h = x.hash;
                    Class<?> kc = null;
                    // 3.如果当前节点x不是根节点, 则从根节点开始查找属于该节点的位置
                    for (TreeNode<K, V> p = root; ; )
                    {
                        int dir, ph;
                        K pk = p.key;
                        // 4.如果x节点的hash值小于p节点的hash值，则将dir赋值为-1, 代表向p的左边查找
                        if ((ph = p.hash) > h)
                            dir = -1;
                        else if (ph < h)
                            dir = 1;
                            // 6.走到这代表x的hash值和p的hash值相等，则比较key值
                        else if ((kc == null &&// 6.1 如果k没有实现Comparable接口 或者 x节点的key和p节点的key相等
                                (kc = comparableClassFor(k)) == null) ||
                                (dir = compareComparables(kc, k, pk)) == 0)
                            dir = tieBreakOrder(k, pk); // 6.2 使用定义的一套规则来比较x节点和p节点的大小，用来决定向左还是向右查找

                        TreeNode<K, V> xp = p;// xp赋值为x的父节点,中间变量用于下面给x的父节点赋值
                        // 7.dir<=0则向p左边查找,否则向p右边查找,如果为null,则代表该位置即为x的目标位置
                        if ((p = (dir <= 0) ? p.left : p.right) == null)
                        {
                            x.parent = xp;
                            if (dir <= 0)
                                xp.left = x;
                            else
                                xp.right = x;
                            // 9.进行红黑树的插入平衡(通过左旋、右旋和改变节点颜色来保证当前树符合红黑树的要求)
                            root = balanceInsertion(root, x);
                            break;
                        }
                    }
                }
            }
            // 10.如果root节点不在table索引位置的头节点, 则将其调整为头节点
            moveRootToFront(tab, root);
        }

        /**
         * Returns a list of non-TreeNodes replacing those linked from
         * this node.
         */
// * 将红黑树节点转为链表节点, 当节点<=6个时会被触发
        final Node<K, V> untreeify(HashMap<K, V> map)
        {
            Node<K, V> hd = null, tl = null;// hd指向头节点, tl指向尾节点
            for (Node<K, V> q = this; q != null; q = q.next)
            {
                // 2.调用replacementNode方法构建链表节点
                Node<K, V> p = map.replacementNode(q, null);
                // 3.如果tl为null, 则代表当前节点为第一个节点, 将hd赋值为该节点
                if (tl == null)
                    hd = p;
                else
                    tl.next = p;
                tl = p; // 5.每次都将tl节点指向当前节点, 即尾节点
            }
            return hd;// 6.返回转换后的链表的头节点
        }

        /**
         * Tree version of putVal.
         */
        //红黑树的put操作，红黑树插入会同时维护原来的链表属性, 即原来的next属性
        final TreeNode<K, V> putTreeVal(HashMap<K, V> map, Node<K, V>[] tab,
                                        int h, K k, V v)
        {
            Class<?> kc = null;
            boolean searched = false;
            // 1.查找根节点, 索引位置的头节点并不一定为红黑树的根节点
            TreeNode<K, V> root = (parent != null) ? root() : this;
            // 2.将根节点赋值给p节点，开始进行查找
            for (TreeNode<K, V> p = root; ; )
            {
                int dir, ph;
                K pk;
                // 3.如果传入的hash值小于p节点的hash值，将dir赋值为-1，代表向p的左边查找树
                if ((ph = p.hash) > h)
                    dir = -1;
                else if (ph < h)
                    dir = 1;
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                else if ((kc == null &&
                        (kc = comparableClassFor(k)) == null) ||
                        (dir = compareComparables(kc, k, pk)) == 0)
                {
                    // 6.1 第一次符合条件, 从p节点的左节点和右节点分别调用find方法进行查找, 如果查找到目标节点则返回
                    if (!searched)
                    {
                        TreeNode<K, V> q, ch;
                        searched = true;
                        if (((ch = p.left) != null &&
                                (q = ch.find(h, k, kc)) != null) ||
                                ((ch = p.right) != null &&
                                        (q = ch.find(h, k, kc)) != null))
                            return q;
                    }
                    // 6.2 否则使用定义的一套规则来比较k和p节点的key的大小, 用来决定向左还是向右查找
                    dir = tieBreakOrder(k, pk);
                }

                TreeNode<K, V> xp = p;// xp赋值为x的父节点,中间变量,用于下面给x的父节点赋值

                // 7.dir<=0则向p左边查找,否则向p右边查找,如果为null,则代表该位置即为x的目标位置
                if ((p = (dir <= 0) ? p.left : p.right) == null)
                {
                    Node<K, V> xpn = xp.next;
                    TreeNode<K, V> x = map.newTreeNode(h, k, v, xpn);
                    if (dir <= 0)
                        xp.left = x;
                    else
                        xp.right = x;
                    xp.next = x;
                    x.parent = x.prev = xp;
                    if (xpn != null)
                        ((TreeNode<K, V>) xpn).prev = x;
                    moveRootToFront(tab, balanceInsertion(root, x));
                    return null;
                }
            }
        }

        /**
         * Removes the given node, that must be present before this call.
         * This is messier than typical red-black deletion code because we
         * cannot swap the contents of an interior node with a leaf
         * successor that is pinned by "next" pointers that are accessible
         * independently during traversal. So instead we swap the tree
         * linkages. If the current tree appears to have too few nodes,
         * the bin is converted back to a plain bin. (The test triggers
         * somewhere between 2 and 6 nodes, depending on tree structure).
         */
        //比普通的红黑树删除节点还要混乱
//        目的就是移除调用此方法的节点，也就是该方法中的 this 节点。移除包括链表的处理和红黑树的处理。
        final void removeTreeNode(HashMap<K, V> map, Node<K, V>[] tab,
                                  boolean movable)
        {
            int n;
            if (tab == null || (n = tab.length) == 0)
                return;
            int index = (n - 1) & hash;
            TreeNode<K, V> first = (TreeNode<K, V>) tab[index], root = first, rl;
            TreeNode<K, V> succ = (TreeNode<K, V>) next, pred = prev;
            if (pred == null)
                tab[index] = first = succ;
            else
                pred.next = succ;
            if (succ != null)
                succ.prev = pred;
            if (first == null)
                return;
            if (root.parent != null)
                root = root.root();
            if (root == null
                    || (movable
                    && (root.right == null
                    || (rl = root.left) == null
                    || rl.left == null)))
            {
                tab[index] = first.untreeify(map);  // too small
                return;
            }
            TreeNode<K, V> p = this, pl = left, pr = right, replacement;
            if (pl != null && pr != null)
            {
                TreeNode<K, V> s = pr, sl;
                while ((sl = s.left) != null) // find successor
                    s = sl;
                boolean c = s.red;
                s.red = p.red;
                p.red = c; // swap colors
                TreeNode<K, V> sr = s.right;
                TreeNode<K, V> pp = p.parent;
                if (s == pr)
                { // p was s's direct parent
                    p.parent = s;
                    s.right = p;
                }
                else
                {
                    TreeNode<K, V> sp = s.parent;
                    if ((p.parent = sp) != null)
                    {
                        if (s == sp.left)
                            sp.left = p;
                        else
                            sp.right = p;
                    }
                    if ((s.right = pr) != null)
                        pr.parent = s;
                }
                p.left = null;
                if ((p.right = sr) != null)
                    sr.parent = p;
                if ((s.left = pl) != null)
                    pl.parent = s;
                if ((s.parent = pp) == null)
                    root = s;
                else if (p == pp.left)
                    pp.left = s;
                else
                    pp.right = s;
                if (sr != null)
                    replacement = sr;
                else
                    replacement = p;
            }
            else if (pl != null)
                replacement = pl;
            else if (pr != null)
                replacement = pr;
            else
                replacement = p;
            if (replacement != p)
            {
                TreeNode<K, V> pp = replacement.parent = p.parent;
                if (pp == null)
                    root = replacement;
                else if (p == pp.left)
                    pp.left = replacement;
                else
                    pp.right = replacement;
                p.left = p.right = p.parent = null;
            }

            TreeNode<K, V> r = p.red ? root : balanceDeletion(root, replacement);

            if (replacement == p)
            {  // detach
                TreeNode<K, V> pp = p.parent;
                p.parent = null;
                if (pp != null)
                {
                    if (p == pp.left)
                        pp.left = null;
                    else if (p == pp.right)
                        pp.right = null;
                }
            }
            if (movable)
                moveRootToFront(tab, r);
        }

        /**
         * Splits nodes in a tree bin into lower and upper tree bins,
         * or untreeifies if now too small. Called only from resize;
         * see above discussion about split bits and indices.
         *
         * @param map   the map
         * @param tab   the table for recording bin heads
         * @param index the index of the table being split
         * @param bit   the bit of hash to split on
         */
        //扩容后，红黑树的hash分布，只可能存在于两个位置：原索引位置、原索引位置+oldCap
        //仅仅resize后被调用
        final void split(HashMap<K, V> map, Node<K, V>[] tab, int index, int bit)
        {
            TreeNode<K, V> b = this;
            // Relink into lo and hi lists, preserving order
            TreeNode<K, V> loHead = null, loTail = null;
            TreeNode<K, V> hiHead = null, hiTail = null;
            int lc = 0, hc = 0;
            for (TreeNode<K, V> e = b, next; e != null; e = next)
            {
                next = (TreeNode<K, V>) e.next;
                e.next = null;
                // 如果e的hash值与老表的容量进行与运算为0,则扩容后的索引位置跟老表的索引位置一样
                if ((e.hash & bit) == 0)
                {
                    if ((e.prev = loTail) == null)
                        loHead = e;
                    else
                        loTail.next = e;
                    loTail = e;
                    ++lc;
                }
                else
                {
                    if ((e.prev = hiTail) == null)
                        hiHead = e;
                    else
                        hiTail.next = e;
                    hiTail = e;
                    ++hc;// 统计原索引位置的节点个数
                }
            }

            // 如果原索引位置的节点不为空
            if (loHead != null)
            {
                //如果节点个数<=6个则将红黑树转为链表结构
                if (lc <= UNTREEIFY_THRESHOLD)
                    tab[index] = loHead.untreeify(map);
                else
                {
                    tab[index] = loHead;
                    //如果hiHead不为空，则代表原来的红黑树(老表的红黑树由于节点被分到两个位置)已经被改变, 需要重新构建新的红黑树
                    if (hiHead != null) // (else is already treeified)
                        //以 loHead 为根节点，构建新的红黑树
                        loHead.treeify(tab);
                }
            }
            //如果索引位置为原索引+oldCap的节点不为空
            if (hiHead != null)
            {
                //如果节点个数<=6个则将红黑树转为链表结构
                if (hc <= UNTREEIFY_THRESHOLD)
                    tab[index + bit] = hiHead.untreeify(map);
                else
                {
                    //将索引位置为原索引+oldCap的节点设置为对应的头节点
                    tab[index + bit] = hiHead;
                    //loHead不为空则代表原来的红黑树(老表的红黑树由于节点被分到两个位置)已经被改变, 需要重新构建新的红黑树
                    if (loHead != null)
                        hiHead.treeify(tab);
                }
            }
        }

        /* ------------------------------------------------------------ */
        // Red-black tree methods, all adapted from CLR

        static <K, V> TreeNode<K, V> rotateLeft(TreeNode<K, V> root,
                                                TreeNode<K, V> p)
        {
            TreeNode<K, V> r, pp, rl;
            if (p != null && (r = p.right) != null)
            {
                if ((rl = p.right = r.left) != null)
                    rl.parent = p;
                if ((pp = r.parent = p.parent) == null)
                    (root = r).red = false;
                else if (pp.left == p)
                    pp.left = r;
                else
                    pp.right = r;
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        static <K, V> TreeNode<K, V> rotateRight(TreeNode<K, V> root,
                                                 TreeNode<K, V> p)
        {
            TreeNode<K, V> l, pp, lr;
            if (p != null && (l = p.left) != null)
            {
                if ((lr = p.left = l.right) != null)
                    lr.parent = p;
                if ((pp = l.parent = p.parent) == null)
                    (root = l).red = false;
                else if (pp.right == p)
                    pp.right = l;
                else
                    pp.left = l;
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        static <K, V> TreeNode<K, V> balanceInsertion(TreeNode<K, V> root,
                                                      TreeNode<K, V> x)
        {
            x.red = true;
            for (TreeNode<K, V> xp, xpp, xppl, xppr; ; )
            {
                if ((xp = x.parent) == null)
                {
                    x.red = false;
                    return x;
                }
                else if (!xp.red || (xpp = xp.parent) == null)
                    return root;
                if (xp == (xppl = xpp.left))
                {
                    if ((xppr = xpp.right) != null && xppr.red)
                    {
                        xppr.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else
                    {
                        if (x == xp.right)
                        {
                            root = rotateLeft(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null)
                        {
                            xp.red = false;
                            if (xpp != null)
                            {
                                xpp.red = true;
                                root = rotateRight(root, xpp);
                            }
                        }
                    }
                }
                else
                {
                    if (xppl != null && xppl.red)
                    {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else
                    {
                        if (x == xp.left)
                        {
                            root = rotateRight(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null)
                        {
                            xp.red = false;
                            if (xpp != null)
                            {
                                xpp.red = true;
                                root = rotateLeft(root, xpp);
                            }
                        }
                    }
                }
            }
        }

        //在进行插入和删除时有可能会触发红黑树的插入平衡调整（balanceInsertion 方法）或删除平衡调整（balanceDeletion 方法）
        static <K, V> TreeNode<K, V> balanceDeletion(TreeNode<K, V> root,
                                                     TreeNode<K, V> x)
        {
            for (TreeNode<K, V> xp, xpl, xpr; ; )
            {
                if (x == null || x == root)
                    return root;
                else if ((xp = x.parent) == null)
                {
                    x.red = false;
                    return x;
                }
                else if (x.red)
                {
                    x.red = false;
                    return root;
                }
                else if ((xpl = xp.left) == x)
                {
                    if ((xpr = xp.right) != null && xpr.red)
                    {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null)
                        x = xp;
                    else
                    {
                        TreeNode<K, V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) &&
                                (sl == null || !sl.red))
                        {
                            xpr.red = true;
                            x = xp;
                        }
                        else
                        {
                            if (sr == null || !sr.red)
                            {
                                if (sl != null)
                                    sl.red = false;
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ?
                                        null : xp.right;
                            }
                            if (xpr != null)
                            {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null)
                                    sr.red = false;
                            }
                            if (xp != null)
                            {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                }
                else
                { // symmetric
                    if (xpl != null && xpl.red)
                    {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null)
                        x = xp;
                    else
                    {
                        TreeNode<K, V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) &&
                                (sr == null || !sr.red))
                        {
                            xpl.red = true;
                            x = xp;
                        }
                        else
                        {
                            if (sl == null || !sl.red)
                            {
                                if (sr != null)
                                    sr.red = false;
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ?
                                        null : xp.left;
                            }
                            if (xpl != null)
                            {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null)
                                    sl.red = false;
                            }
                            if (xp != null)
                            {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }

        /**
         * Recursive invariant check
         */
        static <K, V> boolean checkInvariants(TreeNode<K, V> t)
        {
            TreeNode<K, V> tp = t.parent, tl = t.left, tr = t.right,
                    tb = t.prev, tn = (TreeNode<K, V>) t.next;
            if (tb != null && tb.next != t)
                return false;
            if (tn != null && tn.prev != t)
                return false;
            if (tp != null && t != tp.left && t != tp.right)
                return false;
            if (tl != null && (tl.parent != t || tl.hash > t.hash))
                return false;
            if (tr != null && (tr.parent != t || tr.hash < t.hash))
                return false;
            if (t.red && tl != null && tl.red && tr != null && tr.red)
                return false;
            if (tl != null && !checkInvariants(tl))
                return false;
            if (tr != null && !checkInvariants(tr))
                return false;
            return true;
        }
    }

}

