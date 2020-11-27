package JDK7;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.Serializable;
import java.util.*;


public class HashMap<K, V>
        extends AbstractMap<K, V>
        implements Map<K, V>, Cloneable, Serializable
{

    //默认容量为16,必须是2的幂次方
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4;
    //最大的容量为2的30次方
    static final int MAXIMUM_CAPACITY = 1 << 30;
    //默认负载因子0.75
    static final float DEFAULT_LOAD_FACTOR = 0.75f;
    //空表实例,初始化为这个,直到第一次put操作,才真正是一个Entry数组
    static final Entry<?, ?>[] EMPTY_TABLE = {};

    //transient关键字:将不需要序列化的属性前添加关键字transient
    // 序列化对象的时候，这个属性就不会序列化到指定的目的地中

    //HashMap中实际的数组,数组中每个元素为Entry对象,实际为一个链表
    //开始初始化为空数组,直到第一次put操作,即调用了inflateTable()方法才真正初始化
    transient Entry<K, V>[] table = (Entry<K, V>[]) EMPTY_TABLE;
    //HashMap中已经存储的键值对的数量
    transient int size;
    //下次扩容时的值,即当capacity * load factor时进行扩容
    // If table == EMPTY_TABLE then this is the initial capacity
    int threshold;
    //实际负载因子
    final float loadFactor;
    //记录修改次数,用于fail-fast机制
    transient int modCount;
    //替代哈希阈值默认值,一般不修改这个,也不会怎么用上
    static final int ALTERNATIVE_HASHING_THRESHOLD_DEFAULT = Integer.MAX_VALUE;

    //在Java 8中已经删除了
    //如果不进行特殊设置,基本不会用到
    //替代哈希函数提高映射的性能
    private static class Holder
    {

        //如果不配置,则默认
        // ALTERNATIVE_HASHING_THRESHOLD=threshold=Integer.MAX_VALUE
        //大于他的话才采用备用Hash,所以一般不会用到
        static final int ALTERNATIVE_HASHING_THRESHOLD;

        static
        {
            String altThreshold = java.security.AccessController.doPrivileged(
                    new sun.security.action.GetPropertyAction(
                            "jdk.map.althashing.threshold"));


            int threshold;
            try
            {
                threshold = (null != altThreshold)
                        ? Integer.parseInt(altThreshold)
                        : ALTERNATIVE_HASHING_THRESHOLD_DEFAULT;

                // disable alternative hashing if -1
                if (threshold == -1)
                {
                    threshold = Integer.MAX_VALUE;
                }

                if (threshold < 0)
                {
                    throw new IllegalArgumentException("value must be positive integer.");
                }
            }
            catch (IllegalArgumentException failed)
            {
                throw new Error("Illegal value for 'jdk.map.althashing.threshold'", failed);
            }

            ALTERNATIVE_HASHING_THRESHOLD = threshold;
        }
    }

    //初始化为0,表示禁用替代Hash
    transient int hashSeed = 0;

    //有参构造函数
    public HashMap(int initialCapacity, float loadFactor)
    {
        //三种输入边界问题解决
        if (initialCapacity < 0)
            throw new IllegalArgumentException("Illegal initial capacity: " +
                    initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY)
            initialCapacity = MAXIMUM_CAPACITY;
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new IllegalArgumentException("Illegal load factor: " +
                    loadFactor);

        this.loadFactor = loadFactor;
        threshold = initialCapacity;//初始化为第一个容量大小
        init();//为空
    }

    //传入初始容量,负载因子0.75
    public HashMap(int initialCapacity)
    {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    //无参则容量16,负载因子0.75
    public HashMap()
    {
        this(DEFAULT_INITIAL_CAPACITY, DEFAULT_LOAD_FACTOR);
    }

    //用另一个map初始化
    public HashMap(Map<? extends K, ? extends V> m)
    {
        //先初始化一个Map
        this(Math.max((int) (m.size() / DEFAULT_LOAD_FACTOR) + 1,
                DEFAULT_INITIAL_CAPACITY), DEFAULT_LOAD_FACTOR);
        //threshold此时为初始容量,真正对HashMap里面的数组进行初始化
        inflateTable(threshold);

        putAllForCreate(m);
    }

    /*
    highestOneBit:
    //返回小于等于他的二的幂次方数
    例如10001
    首先i >>  1:     01000
    i |= (i >>  1): i=(10001 | 01000) =11001
    i |= (i >>  2): i=(11001 | 00110) =11111
    ...
    因为int为32位,所以为了保证结果,最后右移16位结束
    使得要求的数字1开始的后面全为1
    11111
    最后的return i - (i >>> 1);
    >>>为无符号右移，忽略符号位，空位都以0补齐
    效果大概为11111-01111=10000
    所以,这样就得到了最高位为1,其他位为0的值
    即为小于等于i的二的幂次方数
    public static int highestOneBit(int i)
    {
        i |= (i >>  1);
        i |= (i >>  2);
        i |= (i >>  4);
        i |= (i >>  8);
        i |= (i >> 16);
        return i - (i >>> 1);
    }

    Integer.highestOneBit((number - 1) << 1)操作:
    如果是单纯的 number << 1,则会找小于等于number << 1的最大二的幂次方数
    就找到了大于等于number的最小幂次方数
    例如15,15<<1=30,highestOneBit(30)=16,16就是大于等于15的最小幂次方数

    这样的问题是,如果传入的是二的幂次方,例如16,则16<<1=32,highestOneBit(32)=32
    就会扩大了一倍
    所以先number-1,就算是16,最后得到的返回值也是16
    保证了肯定是大于等于number的最小幂次方数
     */
    private static int roundUpToPowerOf2(int number)
    {
        return number >= MAXIMUM_CAPACITY
                ? MAXIMUM_CAPACITY
                : (number > 1) ? Integer.highestOneBit((number - 1) << 1) : 1;
    }

    //真正初始化数组操作 传入的是threshold即此时要扩容的大小
    private void inflateTable(int toSize)
    {
        // 找到大于等于他的最小的二的幂次方数
        int capacity = roundUpToPowerOf2(toSize);

        //下一次要扩容的大小
        threshold = (int) Math.min(capacity * loadFactor, MAXIMUM_CAPACITY + 1);
        table = new Entry[capacity];
        //一般则不会进行操作了
        initHashSeedAsNeeded(capacity);
    }

    void init()
    {
    }

    //一般不进行配置,所以默认返回false
    final boolean initHashSeedAsNeeded(int capacity)
    {
        //一般情况下hashSeed一直为0
        //所以currentAltHashing一般为false
        boolean currentAltHashing = hashSeed != 0;

        boolean useAltHashing = sun.misc.VM.isBooted() &&
                (capacity >= Holder.ALTERNATIVE_HASHING_THRESHOLD);
        //异或,若switching要是true,则currentAltHashing,useAltHashing不能相同
        //而currentAltHashing一般为false,所以需要useAltHashing为true
        //要想useAltHashing为true,则capacity >= Holder.ALTERNATIVE_HASHING_THRESHOLD
        //而默认情况Holder.ALTERNATIVE_HASHING_THRESHOLD为Int最大值,所以一般不满足
        //所以useAltHashing一般为false
        //所以switching一般也为false
        boolean switching = currentAltHashing ^ useAltHashing;
        if (switching)
        {
            hashSeed = useAltHashing
                    ? sun.misc.Hashing.randomHashSeed(this)
                    : 0;
        }
        return switching;
    }

    /*
    重新对对象进行hash操作,防止劣质散列函数
    重新hash,让高位的变化也参与数组下标的运算,使得分散更加均匀
    加大hash随机性，使得分布更均匀，从而提高对应数组存储下标位置的随机性
    对原本hashcode扰动,更加均匀
    Null值始终映射到hash 0,index 0
     */
    final int hash(Object k)
    {
        int h = hashSeed;
        if (0 != h && k instanceof String)
        {
            return sun.misc.Hashing.stringHash32((String) k);
        }

        h ^= k.hashCode();

        h ^= (h >>> 20) ^ (h >>> 12);
        return h ^ (h >>> 7) ^ (h >>> 4);
    }

    /* 真正的将hashcode转为数组index的方法
     也是容量必须是二的幂次方的原因
     例如length=16,1 0000
     length-1=0 1111
     h假设为1111010 1101
     h & (length - 1)=1101
     即简单的屏蔽了高位
     因为hashCode假设已经保证了散列均匀,而这样取值范围肯定是0-(length - 1)之间,所以符合要求
    */
    static int indexFor(int h, int length)
    {
        //长度必须是2的非零次幂
        return h & (length - 1);
    }


    public int size()
    {
        return size;
    }

    public boolean isEmpty()
    {
        return size == 0;
    }

    public V get(Object key)
    {
        //因为允许null值,而且null值存在了table[0]
        if (key == null)
            return getForNullKey();
        Entry<K, V> entry = getEntry(key);

        return null == entry ? null : entry.getValue();
    }

    private V getForNullKey()
    {
        if (size == 0)
        {
            return null;
        }
        //在table[0]这个链表中查找,因为可能还是有散列到索引0的非空key
        //所以要遍历一下table[0]链表,直到找到
        for (Entry<K, V> e = table[0]; e != null; e = e.next)
        {
            if (e.key == null)
                return e.value;
        }
        return null;
    }

    public boolean containsKey(Object key)
    {
        return getEntry(key) != null;
    }

    final Entry<K, V> getEntry(Object key)
    {
        if (size == 0)
        {
            return null;
        }

        //put和get都用hashCode方法和自己的hash方法计算得到的,保证相同
        int hash = (key == null) ? 0 : hash(key);
        //先找到散列到的索引的链表
        for (Entry<K, V> e = table[indexFor(hash, table.length)];
             e != null;
             e = e.next)
        {
            Object k;
            //若 hash && key的值相等，则是要找的Entry
            //因为散列到同一个索引的hashCode不一定相同,先判断这个效率更高

            if (e.hash == hash &&
                    ((k = e.key) == key || (key != null && key.equals(k))))
                return e;
        }
        return null;
    }


    public V put(K key, V value)
    {
        if (table == EMPTY_TABLE)
        {
            inflateTable(threshold);
        }
        if (key == null)
            return putForNullKey(value);
        int hash = hash(key);
        int i = indexFor(hash, table.length);
        //与get操作类似,都是查看对应索引的链表是否有key值,有则更新
        for (Entry<K, V> e = table[i]; e != null; e = e.next)
        {
            Object k;
            if (e.hash == hash && ((k = e.key) == key || key.equals(k)))
            {
                V oldValue = e.value;
                e.value = value;
                e.recordAccess(this);
                return oldValue;
            }
        }

        modCount++;
        addEntry(hash, key, value, i);
        return null;
    }

    //存到索引为0的位置
    private V putForNullKey(V value)
    {
        //先在索引为0的地方查找是否有null值的key
        for (Entry<K, V> e = table[0]; e != null; e = e.next)
        {
            //放新值,返回旧值
            if (e.key == null)
            {
                V oldValue = e.value;
                e.value = value;
                e.recordAccess(this);
                return oldValue;
            }
        }
        modCount++;
        addEntry(0, null, value, 0);
        return null;
    }

    //put外界添加元素使用,putForCreate内部构造器使用
    private void putForCreate(K key, V value)
    {
        int hash = null == key ? 0 : hash(key);
        int i = indexFor(hash, table.length);

        for (Entry<K, V> e = table[i]; e != null; e = e.next)
        {
            Object k;
            if (e.hash == hash &&
                    ((k = e.key) == key || (key != null && key.equals(k))))
            {
                e.value = value;
                return;
            }
        }

        createEntry(hash, key, value, i);
    }

    //把Map中的键值对全部放入自己的table中
    private void putAllForCreate(Map<? extends K, ? extends V> m)
    {
        for (Map.Entry<? extends K, ? extends V> e : m.entrySet())
            putForCreate(e.getKey(), e.getValue());
    }


    void resize(int newCapacity)
    {
        Entry[] oldTable = table;
        int oldCapacity = oldTable.length;
        //最大容量则不扩容,只将阈值变成Integer.MAX_VALUE
        if (oldCapacity == MAXIMUM_CAPACITY)
        {
            threshold = Integer.MAX_VALUE;
            return;
        }

        Entry[] newTable = new Entry[newCapacity];
        //initHashSeedAsNeeded(newCapacity)一般为false
        transfer(newTable, initHashSeedAsNeeded(newCapacity));
        table = newTable;
        threshold = (int) Math.min(newCapacity * loadFactor, MAXIMUM_CAPACITY + 1);
    }
    /*
    rehash可看作false
    将旧数组内容放到新数组中来
    会导致bug:两个线程同时对他们操作,他们各种会产生新的table,其中线程一执行完了,新链表变成了C->B->A->null
    线程二在执行e=A,next=B时暂停,等A执行完才继续
    此时下面三行代码:
    e.next = newTable[i];
    newTable[i] = e;
    e = next;
    使得A->null,newTable[i]=A,e=B
    第二次,因为线程一的操作,使得B->A,所以next=A,B->A,newTable[i]=B,e=A
    第三次,next=Null,A->B,newTable[i]=A,e=null
    此时还没有报错,但是产生了循环链表

    C->B->A->B
    线程一table相应索引位置指向C,线程二table相应索引位置指向A
    所以之后如果通过get返回访问这位置时,就会死循环
    */

    void transfer(Entry[] newTable, boolean rehash)
    {
        int newCapacity = newTable.length;
        //遍历数组中每个Entry
        for (Entry<K, V> e : table)
        {
            //对不为空的(链表)进行操作
            while (null != e)
            {
                Entry<K, V> next = e.next;
                if (rehash)
                {
                    e.hash = null == e.key ? 0 : hash(e.key);
                }
                //通过新的容量大小散列得到新的索引
                int i = indexFor(e.hash, newCapacity);
                /*
                假设对链表A->B->C操作,初始e=A,next=B
                 下面的三行代码使得A->null,newTable[i]=A,e=B
                 第二次循环,next=C,B->A->null,newTable[i]=B,e=C
                 第三次循环,next=null,C->B->A->null,e=null.
                 结束循环
                 可见,链表反过来了
                 */
                e.next = newTable[i];
                newTable[i] = e;
                e = next;
            }
        }
    }

    public void putAll(Map<? extends K, ? extends V> m)
    {
        int numKeysToBeAdded = m.size();
        if (numKeysToBeAdded == 0)
            return;

        //还未初始化,则初始化够装得下
        if (table == EMPTY_TABLE)
        {
            inflateTable((int) Math.max(numKeysToBeAdded * loadFactor, threshold));
        }

        //已经初始化过了,但是容量不够,则不断将当前table.length左移
        //直到大于要装的容量
        if (numKeysToBeAdded > threshold)
        {
            int targetCapacity = (int) (numKeysToBeAdded / loadFactor + 1);
            if (targetCapacity > MAXIMUM_CAPACITY)
                targetCapacity = MAXIMUM_CAPACITY;
            int newCapacity = table.length;
            while (newCapacity < targetCapacity)
                newCapacity <<= 1;
            if (newCapacity > table.length)
                resize(newCapacity);
        }

        for (Map.Entry<? extends K, ? extends V> e : m.entrySet())
            put(e.getKey(), e.getValue());
    }

    public V remove(Object key)
    {
        Entry<K, V> e = removeEntryForKey(key);
        return (e == null ? null : e.value);
    }

    //返回的是要删除的那个
    //也是找到要删除的链表,然后将之删除并且返回
    //只是要注意链表删除的细节,如删除头等等
    final Entry<K, V> removeEntryForKey(Object key)
    {
        if (size == 0)
        {
            return null;
        }
        int hash = (key == null) ? 0 : hash(key);
        int i = indexFor(hash, table.length);
        Entry<K, V> prev = table[i];
        Entry<K, V> e = prev;

        while (e != null)
        {
            Entry<K, V> next = e.next;
            Object k;
            if (e.hash == hash &&
                    ((k = e.key) == key || (key != null && key.equals(k))))
            {
                modCount++;
                size--;
                if (prev == e)
                    table[i] = next;
                else
                    prev.next = next;
                e.recordRemoval(this);
                return e;
            }
            prev = e;
            e = next;
        }

        return e;
    }

    //只是将Object转换成entry,再得到key进行删除,和上面操作很类似
    final Entry<K, V> removeMapping(Object o)
    {
        if (size == 0 || !(o instanceof Map.Entry))
            return null;

        Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
        Object key = entry.getKey();
        int hash = (key == null) ? 0 : hash(key);
        int i = indexFor(hash, table.length);
        Entry<K, V> prev = table[i];
        Entry<K, V> e = prev;

        while (e != null)
        {
            Entry<K, V> next = e.next;
            if (e.hash == hash && e.equals(entry))
            {
                modCount++;
                size--;
                if (prev == e)
                    table[i] = next;
                else
                    prev.next = next;
                e.recordRemoval(this);
                return e;
            }
            prev = e;
            e = next;
        }

        return e;
    }

    //清空也会使得修改次数增加
    public void clear()
    {
        modCount++;
        Arrays.fill(table, null);
        size = 0;
    }


    //对应数组的每个链表进行穷举遍历
    //所以尽量不要这样用
    public boolean containsValue(Object value)
    {
        if (value == null)
            return containsNullValue();

        Entry[] tab = table;
        for (int i = 0; i < tab.length; i++)
            for (Entry e = tab[i]; e != null; e = e.next)
                if (value.equals(e.value))
                    return true;
        return false;
    }

    //穷举遍历null值的value
    private boolean containsNullValue()
    {
        Entry[] tab = table;
        for (int i = 0; i < tab.length; i++)
            for (Entry e = tab[i]; e != null; e = e.next)
                if (e.value == null)
                    return true;
        return false;
    }

    //本质就是一个单向链表
    static class Entry<K, V> implements Map.Entry<K, V>
    {
        final K key;
        V value;
        Entry<K, V> next;
        int hash;

        Entry(int h, K k, V v, Entry<K, V> n)
        {
            value = v;
            next = n;
            key = k;
            hash = h;
        }

        public final K getKey()
        {
            return key;
        }

        public final V getValue()
        {
            return value;
        }

        public final V setValue(V newValue)
        {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        //只要键和值的equals方法都相同,则相等
        public final boolean equals(Object o)
        {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry e = (Map.Entry) o;
            Object k1 = getKey();
            Object k2 = e.getKey();
            if (k1 == k2 || (k1 != null && k1.equals(k2)))
            {
                Object v1 = getValue();
                Object v2 = e.getValue();
                if (v1 == v2 || (v1 != null && v1.equals(v2)))
                    return true;
            }
            return false;
        }

        public final int hashCode()
        {
            return Objects.hashCode(getKey()) ^ Objects.hashCode(getValue());
        }

        public final String toString()
        {
            return getKey() + "=" + getValue();
        }


        /*
        默认情况下，在HashMap中，它不执行任何操作。
        在LinkedHashMap中将其重写以维护访问顺序。
        LinkedHashMap的几乎所有代码都在HashMap中，所以存在此方法仅是因为LinkedHashMap需要它。
         */
        void recordAccess(HashMap<K, V> m)
        {
        }


        void recordRemoval(HashMap<K, V> m)
        {
        }
    }


    void addEntry(int hash, K key, V value, int bucketIndex)
    {
        //扩容操作
        if ((size >= threshold) && (null != table[bucketIndex]))
        {
            resize(2 * table.length);
            hash = (null != key) ? hash(key) : 0;
            bucketIndex = indexFor(hash, table.length);
        }

        //放入该值的具体操作
        createEntry(hash, key, value, bucketIndex);
    }

    /*
    首先找到散列到的索引的链表
    采用头插法,将新链表的next指针指向原本的头
    再将该节点赋值给table[bucketIndex]
    操作简单,但是和尾插法效率一样,因为之前都是需要遍历链表查看有没有相同的key
    而且可能会导致一个很糟糕的bug
     */
    void createEntry(int hash, K key, V value, int bucketIndex)
    {
        Entry<K, V> e = table[bucketIndex];
        table[bucketIndex] = new Entry<>(hash, key, value, e);
        size++;
    }



    //迭代器相关操作
    private abstract class HashIterator<E> implements Iterator<E>
    {
        Entry<K, V> next;        // next entry to return
        int expectedModCount;   // 当多个线程对同一个集合的内容进行操作时，就可能会产生fail-fast事件
        int index;              // current slot
        Entry<K, V> current;     // current entry

        HashIterator()
        {
            expectedModCount = modCount;
            if (size > 0)
            { // advance to first entry
                Entry[] t = table;
                //next指向t中第一个有值的链表
                while (index < t.length && (next = t[index++]) == null)
                    ;
            }
        }

        public final boolean hasNext()
        {
            return next != null;
        }

        final Entry<K, V> nextEntry()
        {
            //fail-fast机制
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            Entry<K, V> e = next;
            if (e == null)
                throw new NoSuchElementException();

            if ((next = e.next) == null)
            {
                Entry[] t = table;
                while (index < t.length && (next = t[index++]) == null)
                    ;
            }
            current = e;
            return e;
        }

        public void remove()
        {
            if (current == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            Object k = current.key;
            current = null;
            HashMap.this.removeEntryForKey(k);
            expectedModCount = modCount;
        }
    }

    private final class ValueIterator extends HashIterator<V>
    {
        public V next()
        {
            return nextEntry().value;
        }
    }

    private final class KeyIterator extends HashIterator<K>
    {
        public K next()
        {
            return nextEntry().getKey();
        }
    }

    private final class EntryIterator extends HashIterator<Map.Entry<K, V>>
    {
        public Map.Entry<K, V> next()
        {
            return nextEntry();
        }
    }

    Iterator<K> newKeyIterator()
    {
        return new KeyIterator();
    }

    Iterator<V> newValueIterator()
    {
        return new ValueIterator();
    }

    Iterator<Map.Entry<K, V>> newEntryIterator()
    {
        return new EntryIterator();
    }


    int capacity()
    {
        return table.length;
    }

    float loadFactor()
    {
        return loadFactor;
    }



    // Views
    private transient Set<Map.Entry<K, V>> entrySet = null;

    public Set<K> keySet()
    {
        Set<K> ks = keySet;
        return (ks != null ? ks : (keySet = new KeySet()));
    }


    private final class KeySet extends AbstractSet<K>
    {
        public Iterator<K> iterator()
        {
            return newKeyIterator();
        }

        public int size()
        {
            return size;
        }

        public boolean contains(Object o)
        {
            return containsKey(o);
        }

        public boolean remove(Object o)
        {
            return HashMap.this.removeEntryForKey(o) != null;
        }

        public void clear()
        {
            HashMap.this.clear();
        }
    }

    public Collection<V> values()
    {
        Collection<V> vs = values;
        return (vs != null ? vs : (values = new Values()));
    }

    private final class Values extends AbstractCollection<V>
    {
        public Iterator<V> iterator()
        {
            return newValueIterator();
        }

        public int size()
        {
            return size;
        }

        public boolean contains(Object o)
        {
            return containsValue(o);
        }

        public void clear()
        {
            HashMap.this.clear();
        }
    }

    public Set<Map.Entry<K, V>> entrySet()
    {
        return entrySet0();
    }

    private Set<Map.Entry<K, V>> entrySet0()
    {
        Set<Map.Entry<K, V>> es = entrySet;
        return es != null ? es : (entrySet = new EntrySet());
    }

    private final class EntrySet extends AbstractSet<Map.Entry<K, V>>
    {
        public Iterator<Map.Entry<K, V>> iterator()
        {
            return newEntryIterator();
        }

        public boolean contains(Object o)
        {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<K, V> e = (Map.Entry<K, V>) o;
            Entry<K, V> candidate = getEntry(e.getKey());
            return candidate != null && candidate.equals(e);
        }

        public boolean remove(Object o)
        {
            return removeMapping(o) != null;
        }

        public int size()
        {
            return size;
        }

        public void clear()
        {
            HashMap.this.clear();
        }
    }



    //浅层次拷贝,拷贝对象改变会影响被拷贝的对象
    public Object clone()
    {
        HashMap<K, V> result = null;
        try
        {
            result = (HashMap<K, V>) super.clone();
        }
        catch (CloneNotSupportedException e)
        {
            // assert false;
        }
        if (result.table != EMPTY_TABLE)
        {
            result.inflateTable(Math.min(
                    (int) Math.min(
                            size * Math.min(1 / loadFactor, 4.0f),
                            // we have limits...
                            HashMap.MAXIMUM_CAPACITY),
                    table.length));
        }
        result.entrySet = null;
        result.modCount = 0;
        result.size = 0;
        result.init();
        result.putAllForCreate(this);

        return result;
    }

    /*
    为了HashMap的序列化而创建
    设置为私有的原因:
    如果实现了一个继承HashMap的类，也想有自己的序列化和反序列化方法，
    那也可以实现私有的readObject和writeObject方法，而不用关心HashMap自己的那一部分。

    在实现序列化的时候，如果该类实现了writeObject和readObject这两个方法那么就会调用该类的实现
    如果没有的话就会使用defaultWriteObject()和defaultReadObject()
     */
    private void writeObject(java.io.ObjectOutputStream s)
            throws IOException
    {
        // Write out the threshold, loadfactor, and any hidden stuff
        s.defaultWriteObject();

        // Write out number of buckets
        if (table == EMPTY_TABLE)
        {
            s.writeInt(roundUpToPowerOf2(threshold));
        }
        else
        {
            s.writeInt(table.length);
        }

        // Write out size (number of Mappings)
        s.writeInt(size);

        // Write out keys and values (alternating)
        if (size > 0)
        {
            for (Map.Entry<K, V> e : entrySet0())
            {
                s.writeObject(e.getKey());
                s.writeObject(e.getValue());
            }
        }
    }

    //Java的序列化机制是通过在运行时判断类的serialVersionUID来验证版本一致性的
    private static final long serialVersionUID = 362498820763181265L;

    private void readObject(java.io.ObjectInputStream s)
            throws IOException, ClassNotFoundException
    {
        // Read in the threshold (ignored), loadfactor, and any hidden stuff
        s.defaultReadObject();
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
        {
            throw new InvalidObjectException("Illegal load factor: " +
                    loadFactor);
        }

        // set other fields that need values
        table = (Entry<K, V>[]) EMPTY_TABLE;

        // Read in number of buckets
        s.readInt(); // ignored.

        // Read number of mappings
        int mappings = s.readInt();
        if (mappings < 0)
            throw new InvalidObjectException("Illegal mappings count: " +
                    mappings);

        // capacity chosen by number of mappings and desired load (if >= 0.25)
        int capacity = (int) Math.min(
                mappings * Math.min(1 / loadFactor, 4.0f),
                // we have limits...
                HashMap.MAXIMUM_CAPACITY);

        // allocate the bucket array;
        if (mappings > 0)
        {
            inflateTable(capacity);
        }
        else
        {
            threshold = capacity;
        }

        init();  // Give subclass a chance to do its thing.

        // Read the keys and values, and put the mappings in the HashMap
        for (int i = 0; i < mappings; i++)
        {
            K key = (K) s.readObject();
            V value = (V) s.readObject();
            putForCreate(key, value);
        }
    }
}
