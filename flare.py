# coding: UTF-8
#from gurobipy import *
import numpy as np
import csv
import time
import hashlib
import matplotlib.pyplot as plt
import networkx as nx
import secrets
import ecdsa
import base58
import random
import math
import copy
import queue

MAX_CAP = 100
MIN_CAP = 10
NUM_NODE = 20 #ネットワークのノードの数
PROB_EDGE = 0.3 #ノード間にチャネルが存在する確率
RNB = 2 #近隣半径
NBC = 5 #ビーコンの数
#Ntab = 10 ルート検索中のクエリ対象ノードの最大数
num_DJ = 0

class Generater(): 
    #ビットコインアドレスを生成する。このうちpubkeyがライトニングネットワークIDに相当し、アドレス距離を求めるのに使用する
    def __init__(self):
        p = 2**256-2**32-2**9-2**8-2**7-2**6-2**4-1
        self.new_privkey(p)
        self.new_pubkey()
        self.new_address(bytes.fromhex("00"))

    def new_privkey(self, p):
        privkey = secrets.randbelow(p)
        privkey = format(privkey, 'x')
        self.privkey = privkey.zfill(64)

    def new_pubkey(self):
        bin_privkey = bytes.fromhex(self.privkey)
        signing_key = ecdsa.SigningKey.from_string(bin_privkey, curve = ecdsa.SECP256k1)
        verifying_key = signing_key.get_verifying_key()
        pubkey = bytes.fromhex("04") + verifying_key.to_string()
        self.pubkey = pubkey.hex()

    def new_address(self, version):
        ba = bytes.fromhex(self.pubkey)
        digest = hashlib.sha256(ba).digest()
        new_digest = hashlib.new('ripemd160')
        new_digest.update(digest)
        pubkey_hash = new_digest.digest()

        pre_address = version + pubkey_hash
        address = hashlib.sha256(pre_address).digest()
        address = hashlib.sha256(address).digest()
        checksum = address[:4]
        address = pre_address + checksum
        address = base58.b58encode(address)
        self.address = address.decode()
        #print("Address = " + self.address)


class Node:
    def __init__(self, n):
        self.name = n
        key = Generater()
        self.address = key.address
        self.pubkey = key.pubkey
        self.RT = set() #ルーティングテーブル。セットとして実装 (u, v) u,v in V
        self.path = dict() #self.path[r]:ノードrへの最短経路
        self.cap = dict() #辞書型として実装
        self.adj = list() #距離1の範囲内にある(直接チャネルで繋がっている)ノードのリスト
        self.bc = set() #ビーコンを格納する
        self.rb = list() #selfをビーコンとして選択したノードのリスト
        self.fee = dict()
        self.nb = list() #このノードの近傍を記録するリスト
        self.dist = dict() #各ノードへの最短距離を格納する
        self.M = set() #RTに新しく追加されたチャネルを記録
        self.Mr = set() #RTから削除されたチャネルを記録
        self.active = 1 #ノードがアクティブになっているかを記録する。1ならアクティブ、0ならノンアクティブ
        self.candicate = dict() #self.candicate[r]:ノードrへの候補ルートのリスト。dict(list())

    def print_node(self):
        print("name {}, adj {}, RT {}".format(self.name, self.adj, self.RT))

    def set_adj_edge(self, e):
        if self in e:
            self.RT.add(e)
            m = list(e)
            m.remove(self)
            if e[0] == self:
                self.path[m[0]] = e
            else:
                self.path[m[0]] = e[::-1]
            self.adj.append(m[0])
            self.dist[m[0]] = 1

    def BEACON_ACK(self, u):
        #u：ビーコンを見つけたいノード。送信者
        #selfよりアドレス距離がuに近いノードzを探す。あればノードの集合Cvとそのノードへのパスの集合Mvを返す
        node = Nodes(list(self.RT))
        node.remove(self)
        if u in node:
            node.remove(u) #ビーコンの候補から自身とメッセージの送信者を除外
        B = node
        Cv = set()
        Mv = dict()
        while B:
            ahop = hop_address(self, u)
            for z in list(B):
                each_hop = hop_address(u, z)
                if each_hop < ahop:
                    Cv.add(z)
                    Mv[z] = list(self.path[z])
                B.remove(z)
        return Cv, Mv
    
    def TABLE_REQ(self, v):
        #送信者selfが受信者vにルーティングテーブルを要求する
        self.RT = self.RT | v.RT #RTをマージ
        vpath = self.path[v]
        for k in v.path.keys():
            #selfがvの近隣ノードkまでのパスを持っていなければvを経由してkに行くパスを追加
            if k not in self.path.keys():
                self.path[k] = vpath + v.path[k]
            else:
                if len(self.path[k]) > len(vpath + v.path[k]):
                    self.path[k] = vpath + v.path[k]
                else:
                    continue
    
    def delete(self, e):
        #selfのRTからeを削除し、削除した辺の集合Mrにeを追加、更新した頂点の集合Vupdに自信を追加
        #cap.path,feeからも対応する辺を削除
        if e[::-1] in self.RT:
            e = e[::-1]

        if e in self.RT:
            self.RT.remove(e)
            self.Mr.add(e)
            self.cap.pop(e)
            self.cap.pop(e[::-1])
            self.fee.pop(e)
            self.fee.pop(e[::-1])
            u = list(e)
            if self in u:
                u.remove(self)
            for ei in u:
                if ei in self.dist.keys():
                    self.dist.pop(ei)
                    self.path.pop(ei)
                if ei in self.adj:
                    self.adj.remove(ei)

    def Add(self, e, ncap, nfee, F):
        self.set_adj_edge(e)
        self.cap[e] = self.cap[e[::-1]] = ncap
        self.fee[e] = self.fee[e[::-1]] = F[e] = F[e[::-1]] = nfee
        self.M.add(e)
        u = list(e)
        u.remove(self)
        self.M = self.M & u[0].RT

def plotLN(V, E):
    #作成したネットワークをプロットして確認する用
    #V：Nodeクラスの集合　E：辺の集合(多分いらない)
    edge = set()
    G = nx.DiGraph()
    for e in E:
        edge.add((e[0].name, e[1].name))
    G.add_edges_from(edge)
    nx.draw_networkx(G)
    plt.show()

def Nodes(T):
    #エッジの集合Tに含まれるノードを取り出す Nodes(T) := {A : (A,・) in T ^ (・,A) in T}
    V = set()
    for n in range(len(T)):
        V = V.union(T[n])
    return V

def Dijkstra(s, g, G, cap):
    #ダイクストラ法を用いて始点sから終点gまでの最短経路、距離を探索する
    #G：探索を行うグラフ G = (V, E) V=n：グラフに含まれるノード E=(u,v)：グラフの辺
    #distance：始点から各ノードまでの最短距離
    #previous_node：始点から各ノードへ最短経路で移動する際に、直前に通るノード

    if s not in G[0] or g not in G[0]: #始点、終点がグラフになければエラー
        return math.inf, []

    global num_DJ
    #print("Dijkstra start {}".format(num_DJ))
    num_DJ += 1
    distance = dict()
    previous_node = dict()
    for i in G[0]:
        distance[i] = math.inf
        previous_node[i] = -1
    distance[s] = 0
    unsearched_node = list(G[0])
    E = G[1]
    while unsearched_node:
        min_dist = math.inf
        for each_node in unsearched_node:
            if distance[each_node] < min_dist:
                min_dist = distance[each_node]
                target_node = each_node
        if target_node == g or min_dist == math.inf:
            break
        unsearched_node.remove(target_node)
        each_dist = dict()
        for i in range(len(E)):
            if target_node in E[i]:
                key = list(E[i])
                key.remove(target_node)
                if key[0] in unsearched_node:
                    each_dist[key[0]] = cap[E[i]]
        for k in each_dist.keys():
            if distance[k] > distance[target_node] + each_dist[k]:
                distance[k] = min(distance[k], distance[target_node] + each_dist[k])
                previous_node[k] = target_node
    
    path = [g]
    current = g
    while previous_node[current] != -1:
        path.insert(0, previous_node[current])
        current = previous_node[current]
    return distance[g], tuple(path)  #始点から終点までの最短距離とパスを返す

def Yen_Algorithm(s, g, G, cap, k):
    #始点sから終点gに至るまでの経路の中で１番目からk番目に短いパスを作成する
    #k：発見するパスの数
    A = list() #第k最短経路を格納する
    B = list() #最短経路の候補を格納する
    #まず第１最短経路をダイクストラで探索
    kn = Dijkstra(s, g, G, cap)
    if kn[0] == math.inf:
        return ()
    A.append(kn) #A[i][0]：パスの長さ　A[i][1]：パス
    while len(A) < k:
        kpath = A[-1][1]
        cap_yen = dict()
        for key in cap.keys():
            cap_yen[key] = cap[key]
        #Aの要素の中で最も長いパスを選択し、その中から分岐ノードを決定。対応するエッジの重みを無限に
        for i in range(len(kpath)-1):
            squr_root = list()
            squr_dist = 0
            v = kpath[i] #パスの先頭から順に分岐ノードにして行く
            #kpathの始点から分岐ノードまでのパスをsqur_rootとして記憶  
            squr_root = kpath[0:i]
            for n in range(i): #ここi-1じゃなくてi？
                squr_dist += cap[(kpath[n], kpath[n+1])]
            for a in A: #第k最短経路の中で分岐ノードを含むパスを探す
                if v in a[1]:
                    key = a[1].index(v)
                    e = (a[1][key], a[1][key+1])
                    #分岐ノードから伸びる辺の重みを無限にして通れなくする
                    cap_yen[e] = math.inf
                    cap_yen[e[::-1]] = math.inf
            kn = Dijkstra(v, g, G, cap_yen)
            path = (kn[0]+squr_dist, squr_root + kn[1])

            #ここ間違ってた。なぜか重みを無限にしたはずの辺を普通に通っちゃってる。e[::-1]も重みを無限にすればいい？

            if path[0] == math.inf:
                continue
            j = 0
            flag = 1
            for j in range(len(B)):
                #パスknがBに含まれていない場合、ソートしながらBに格納。含まれていれば何もしない
                if B[j][1] == path[1]:
                    flag = 0
                    break
                if B[j][0] > path[0]:
                    flag = 1
                    break
                if j == len(B)-1:
                    j+=1
            if flag == 1:
                B.insert(j, path)
        if len(B) == 0:
            break
        A.append(B[0]) #候補パスの中で最も短いものをAに追加。Bはソート済みなのでB[0]を取り出せば良い
        B.remove(B[0])
    return [row[1] for row in A]

def check_path(p):
    for v in p:
        if v.active == 0:
            return False
    for i in range(len(p)-1):
        if p[i+1] not in p[i].adj:
            return False
    return True

def dchan(u, e, G, cap):
    #グラフGにおいて、ノードuからチャネルeまでの最小距離を計算する
    #G = (V, E), u in V, e in E
    #dchan(u,e,G) = dchan(u, (x,y), G):= min{ dnode(u,x), dnode(u,y)} u,x,y
    #dnode(x,y)：ノードx,y間の最小距離

    if e[0] not in u.dist.keys():
        D1 = Dijkstra(u, e[0], G, cap)
        u.path[e[0]] = D1[1]
        e[0].path[u] = D1[1][::-1]
        u.dist[e[0]] = e[0].dist[u] = D1[0]
    else:
        if check_path(u.path[e[0]]):
            D1 = (u.dist[e[0]], u.path[e[0]])
        else:
            D1 = Dijkstra(u, e[0], G, cap)
            u.path[e[0]] = D1[1]
            e[0].path[u] = D1[1][::-1]
            u.dist[e[0]] = e[0].dist[u] = D1[0]
    if e[1] not in u.dist.keys():
        D2 = Dijkstra(u, e[1], G, cap)
        u.path[e[1]] = D2[1]
        e[1].path[u] = D2[1][::-1]
        u.dist[e[1]] = e[1].dist[u] = D2[0]
    else:
        if check_path(u.path[e[1]]):
            D2 = (u.dist[e[1]], u.path[e[1]])
        else:
            D2 = Dijkstra(u, e[1], G, cap)
            u.path[e[1]] = D2[1]
            e[1].path[u] = D2[1][::-1]
            u.dist[e[1]] = e[1].dist[u] = D2[0]
    return min(D1[0], D2[0])


def RT_UPD(u, v, M, Mr):
    #u：メッセージを受信するノード v：メッセージを送信するノード M：新しく開いたチャネルのリスト Mr：閉じたチャネルのリスト
    #受信ノードuのルーティングテーブルu.RTを更新する
    RTpre = list(u.RT | set(M))
    Gpre = (Nodes(RTpre), RTpre)
    Mnew = set(M) - u.RT

    for e in Mnew:
        cap = dict()
        cap.update(u.cap)
        cap.update(v.cap)
        for k in cap.keys():
            cap[k] = 1
        dc = dchan(u, e, Gpre, cap)
        if dc <= RNB: #ここ<=にしないとRTが足りない
            u.RT.add(e)
            u.cap[e] = u.cap[e[::-1]] = v.cap[e]
            u.fee[e] = u.fee[e[::-1]] = v.fee[e]

    for e in set(Mr) & u.RT:
        u.delete(e)

def hop_address(u, v):
    #ノードu,v感のアドレス距離を計算する
    #アドレス距離はノードのアドレスのXORで求められる
    if type(u) is not Node or type(v) is not Node:
        print("u or v is not Node.")
    
    return int(u.pubkey, 16) ^ int(v.pubkey, 16) 

def Beacon_Discovery(u, Nbc, F):
    node = Nodes(list(u.RT))
    node.remove(u)
    B = set(node)
    U = set()
    R = list()
    zpath = dict()
    #候補ノードを発見する。Bは候補になるか確認するノード。Uは確認が終わったノード。Rは候補ノード
    while B:
        ahop = math.inf
        for v in B:
            #ビーコン候補とするノードeach_nodeを決定する
            each_hop = hop_address(u, v)
            if each_hop < ahop:
                ahop = each_hop
                each_node = v
        #探索済みノードの集合Uにeach_nodeを追加し、未探索ノード集合Bから削除
        U.add(each_node)
        B.remove(each_node)
        #each_nodeのRT内にさらにビーコンにふさわしいノードがあるか探索。終わったらビーコン候補集合Rにeach_nodeを追加
        Cv, Mv = each_node.BEACON_ACK(u)
        R.append(each_node)
        #候補ノードへのパスの集合zpathにuからeach_nodeまでのパスを追加
        zpath[each_node] = u.path[each_node]
        for z in Cv - (B & U):
            if hop_address(z, u) < hop_address(each_node, u):
                if Mv[z][0] == each_node and Mv[z][-1] == z:
                    B.add(z)
                    Mv[z].remove(each_node)
                    new_path = u.path[each_node] + tuple(Mv[z])
                    if z not in u.path.keys():
                        u.path[z] = new_path
                    else:
                        if len(u.path[z]) > len(new_path):
                            u.path[z] = new_path
        while len(B) > Nbc:
            zstar = 0
            pl = math.inf
            for z in B:
                if len(u.path[z]) < pl:
                    zstar = z
                    pl = len(u.path[z])
            B.remove(zstar)
    
    #Rをソートする
    Rsort = list()
    Rsort.append(R[0])
    for i in range(1, len(R)):
        #R[i]について、Rsortを先頭から見て送信者とのアドレス距離が自分より遠くなるインデックスを探す
        each_hop = hop_address(u, R[i])
        k = len(Rsort)
        index = 0
        for j in range(k):
            if each_hop < hop_address(u, Rsort[j]):
                #R[i]よりRsort[j]の方がアドレス距離が遠くなるならindex=jとし反復を抜ける
                Rsort.insert(index, R[i])
                break
            if j == k-1:
                Rsort.append(R[i])

    for v in Rsort:
        if len(u.bc) == Nbc:
            break
        if v in zpath.keys():
            u.bc.add(v)
            for i in range(len(zpath[v])-1):
                e = (zpath[v][i], zpath[v][i+1])
                #ここでeのルーティングテーブルも更新しないとこの後おかしくなる
                u.RT.add(e)
                u.fee[e] = u.fee[e[::-1]] = F[e]
                u.cap[e] = u.cap[e[::-1]] = e[0].cap[e]
                if zpath[v][i+1] not in u.path.keys():
                    u.path[zpath[v][i+1]] = zpath[v][0:i+2]
                    u.dist[zpath[v][i+1]] = len(zpath[v][0:i+2])
            u.path[v] = zpath[v]
            u.dist[v] = len(zpath[v])
            v.rb = u
    

def Candicate_rotes(s, r, k, f, Ntab):
    #送信者sから受信者rへの送金ルートをk本発見する
    #Ntab：ルーティングテーブルを要求するノードの最大数。Ntab個以上のノードにルーティングテーブルを要求しない
    #f：送金額。評価値の計算に使うかも
    RTco = s.RT
    P = set() #候補ルートを格納するリスト。重複を起こさないためsetにしている
    U = set() #ルーティングテーブルを取得した受信者に近いノードのリスト
    fee = dict()
    cap = dict()
    rr = dict() #パスpの評価値を格納する
    Mbar = set()

    #もしs-r間に既知のパスがあり、経由するノード全てがアクティブでチャネルが消えてないならそのパスをそのまま使う。
    if r in s.candicate.keys():
        for path in s.candicate[r]:
            if check_path(path):
                P.add(path)
                rr[path] = route_ranking(f, path)
            else:
                s.candicate[r].remove(path)

    #ここでcapが送金額より少ないチャネルを除外する。これがあるせいで送金できないパスを見つけてしまい目標の本数まで至っていない
    cap.update(s.cap)
    for key in s.fee.keys():
        fee[key] = s.fee[key]
    while len(P) < k and len(U) <= Ntab:
        for e in RTco:
            if cap[e] < f:
                Mbar.add(e)
        RTco = RTco - Mbar
        G = (Nodes(list(RTco)), list(RTco))
        beacon = G[0] | {r}
        path = Yen_Algorithm(s, r, G, fee, k) #同じパスが返ってきてる
        for pi in path:
            rr[pi] = route_ranking(f, pi)
            if rr[pi] != -math.inf:
                #評価値が-infでなければリストに追加
                P.add(pi)
        if len(P) < k:
            ahop = math.inf
            for b in beacon - U:
                each_hop = hop_address(r, b)
                if ahop > each_hop:
                    ahop = each_hop
                    c = b
            RTco = RTco | c.RT
            fee.update(c.fee)
            cap.update(c.cap)
            U.add(c)
    #発見した候補ルートを記録
    s.candicate[r] = P
    return P, rr

def route_ranking(f, p):
    #Yen_Algorithmによって発見したルートをランキング付けするための評価値を返す
    #f：送金額　p：パス
    C = 0
    for i in range(len(p)-1):
        e = (p[i], p[i+1])
        if p[i].cap[e] < f:
            return -math.inf
        else:
            C += p[i].fee[e]
    return 1/C
        
def make_network():
    knb = 4
    V = [Node(n) for n in range(NUM_NODE)]
    #ネットワークが円環状になるようにエッジを貼る
    E = [(V[i], V[i+1]) for i in range(NUM_NODE-1)]
    E.append((V[NUM_NODE-1], V[0]))
    F = {(i,j):math.inf for i in V for j in V}

    #最近傍の数がknb個になるように近くのノードとエッジを貼る
    for i in range(NUM_NODE):
        for n in range(2,(knb//2)+1):
            E.append((V[i-n], V[i]))

    Emiddle = copy.copy(E) #張替え後のエッジを格納する
    #全ての辺について確率PROB_EDGEで張替える。
    for e in E:
        if random.random() < PROB_EDGE:
            #貼り替える場合ランダムに頂点vを1つ選択し、辺(e[0],v)がすでに存在しなければ追加、元の辺を削除
            v = random.choice(V)
            if e[0] != v and (e[0], v) not in Emiddle and (v, e[0]) not in Emiddle:
                Emiddle.remove(e)
                if e[0].name < v.name:
                    e = (e[0], v)
                else:
                    e = (v, e[0])
                Emiddle.append(e)
        #エッジを張り替えるかの処理が終わったら、そのエッジは確定するので隣接とcap,feeを処理する
        e[0].set_adj_edge(e)
        e[1].set_adj_edge(e)
        e[0].cap[e] = e[0].cap[e[::-1]] = \
        e[1].cap[e] = e[1].cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
        e[0].fee[e] = e[0].fee[e[::-1]] = \
        e[1].fee[e] = e[1].fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)

    print("|V|={}, |E|={}".format(len(V), len(Emiddle)))

    for v in range(NUM_NODE):
        for u in V[v].adj:
            RT_UPD(V[u.name], V[v], V[v].RT, {})
            if len(V[v].cap) != len(V[v].RT)*2:
                print("hoge")
    return V, Emiddle, F

def LN_UPD(V, E, F):
    #LNを更新する。V：更新前のLNの頂点集合 E：辺集合 F：重みの集合
    Eadd = 10
    Vadd = 5
    Edel = 10 #追加、削除する辺、頂点の数
    Vdel = 3
    Vupd = set() #RTが更新されたノードの集合

    ebar = random.sample(E, Edel)
    vbar = random.sample(V, Vdel)

    print("evar=(",end="")
    #辺を消す
    for j in range(len(ebar)):
        e = ebar[j]
        print("({}, {}), ".format(ebar[j][0].name, ebar[j][1].name), end="")
        E.remove(e)
        e[0].delete(e)
        e[1].delete(e)
        Vupd.add(e[0])
        Vupd.add(e[1])
        NEIGHBOR_UPD(Vupd)
    print(")")

    print("vbar=(",end = "")
    #ノードをノンアクティブにする
    for v in vbar:
        print(v.name, ", ", end="")
        for u in v.adj:
            v.active = 0
            e = (v, u)
            u.delete(e)
            Vupd.add(u)
            NEIGHBOR_UPD(Vupd)
    print(")")

    #新しいチャネルを追加    
    add_num = 0
    print("new edge=(",end="")
    while add_num < Eadd:
        e = tuple(random.sample(V, 2))
        print("({}, {}), ".format(e[0].name, e[1].name), end="")
        if e not in E and e[::-1] not in E:
            cap = random.randint(MIN_CAP, MAX_CAP)
            fee = random.randint(1, 10)
            e[0].Add(e, cap, fee, F)
            e[1].Add(e, cap, fee, F)
            Vupd.add(e[0])
            Vupd.add(e[1])
            add_num += 1
            NEIGHBOR_UPD(Vupd)
    print(")")

    #新しいノードを追加
    add_num = 0
    print("new node=", end = "")
    lenV = len(V)
    while add_num < Vadd:
        adj = random.sample(V, 4)
        v = Node(lenV + add_num + 1)
        V.append(v)
        print(v.name, ", ", end="")
        for u in adj:
            e = (u, v)
            cap = random.randint(MIN_CAP, MAX_CAP)
            fee = random.randint(1, 10)
            e[0].Add(e, cap, fee, F)
            e[1].Add(e, cap, fee, F)
            Vupd.add(u)
            Vupd.add(v)
            NEIGHBOR_UPD(Vupd)
        add_num += 1
    print("")
        

def NEIGHBOR_UPD(Vupd):
    while Vupd:
        v = list(Vupd)[0]
        #print("UPD ",v.name)
        for u in v.adj:
            RT_UPD(u, v, v.M, v.Mr)
            #受信ノードuのRTが更新されていたらVupdに追加
            if len(u.M) > 0 or len(u.Mr) > 0: 
                Vupd.add(u)
        #送信ノードvのM,Mrを一度初期化
        v.M = set()
        v.Mr = set()
        Vupd.remove(v)


def check_RT(v, F1):
    #応急措置
    #ノードvのRTに含まれるエッジe=(x,y)についてvからx,yそれぞれへのパスと距離が登録されているかを確認、
    #なければ追加する。
    #本来RT内に存在するノードへの距離は全て把握しているはずだから、こんなことしなくていい
    #どっかバグってる
    for e in v.RT:
        RTpre = list(v.RT)
        Gpre = (Nodes(RTpre), RTpre)
        if e[0] not in v.path.keys() or e[1] not in v.path.keys():
            dchan(v, e, Gpre, F1)
            

def pathplot(path, rr):
    print("(", end="")
    for i in range(len(path)-1):
        print("{}, ".format(path[i].name), end="")
    print("{}), {}".format(path[-1].name, rr))

def Simulation1(V, E, F):
    G = (V, E)
    accessible = {0:[0 for n in range(12)], 1:[0 for n in range(12)], 10:[0 for n in range(12)]}
    num_sample = 10
    num_r = NUM_NODE//10
    num_culc = num_sample * num_r
    Q = (0, 1, 10)
    s = random.sample(V, num_sample) #送信者のリスト
    r_samp = random.sample(V, num_r) #受信者のリスト
    length = {0:[0 for n in range(12)], 1:[0 for n in range(12)], 10:[0 for n in range(12)]}
    Fstar = {}
    for key in F.keys():
        Fstar[key] = 1
    ts = time.time()
    print("average time")
    print("Nbc 0 1 10")
    for i in range(12): #ビーコンの数
        avetime = {0:0, 1:0, 10:0}
        for j in range(num_sample): #送金を行うノード候補のリストsのインデックス
            Beacon_Discovery(s[j], i, F)
            for r in r_samp:
                if s[j] != r:
                    for tab in Q:
                        t1 = time.time()
                        P, rr = Candicate_rotes(s[j], r, 5, 10, tab)
                        t2 = time.time()
                        avetime[tab] += t2 - t1
                        if len(P) != 0:
                            Ddk, Pdk = Dijkstra(s[j], r, G, Fstar)
                            #for pi in P:
                            #    pathplot(pi, rr[pi])
                            accessible[tab][i] += 1
                            maxp = max(rr, key=rr.get)
                            length[tab][i].append(len(maxp) - len(Pdk))
        print("{} {} {} {}".format(i, avetime[0]/num_culc, avetime[1]/num_culc, avetime[10]/num_culc))
    te = time.time()
    print("Accessible")
    print("Nbc 0 1 10 exxess")
    for n in range(12):
        print("{} {} {} {} {}".format(n, accessible[0][n]/num_culc, accessible[1][n]/num_culc, accessible[10][n]/num_culc, sum(length)/len(length)))
    #print("average_time = {}".format(avetime/(num_culc*12*3)))
    print("total_time = {}".format(te-ts))

def Simulation2(V, E, F):
    G = (V, E)
    accessible = [0 for n in range(12)]
    s = random.sample(V, 10)
    length = []
    excess = dict()
    Fstar = {(i,j):1 for i in range(NUM_NODE) for j in range(NUM_NODE)}
    for v in range(NUM_NODE):
        Fstar[(v, v)] = 0
    for i in range(12): #ビーコンの数
        print("Nbc = {}.search start".format(i))
        for j in range(10): #送金を行うノード候補のリストsのインデックス
            Beacon_Discovery(s[j], i, F)
            for m in range(100):
                In = 'c'
                while In == 'c':
                    r = random.choice(V)
                    if s[j] != r:
                        t1 = time.time()
                        #s[j]からrへ10BTC送金するパスを最大5本発見する。10BTCは現在の実装で全てのパスが送金できる最低額
                        P, rr = Candicate_rotes(s[j], r, 5, 10, 10)
                        t2 = time.time()
                        Ddk, Pdk = Dijkstra(s[j], r, G, Fstar)
                        if len(P) != 0:
                            for pi in P:
                                pathplot(pi, rr[pi])
                            accessible[i] += 1
                            maxp = max(rr, key=rr.get)
                            if len(maxp) < len(Pdk):
                                print("okasii")
                            length.append(len(maxp) - len(Pdk))
                        print("time: {}[s]".format(t2-t1))
                        In = input("Current(c) or Next(n): ")
        excess[i] = sum(length)/len(length)
    print("Nbc accessible excess")
    for n in range(1):
        print("{} {} {}".format(n, accessible[n]/1000, excess[n]))

def Simulation3(V, E, F):
    #ダイクストラで最短経路を求めない
    G = (V, E)
    accessible = {0:[0 for n in range(12)], 1:[0 for n in range(12)], 10:[0 for n in range(12)]}
    num_sample = 10
    num_r = NUM_NODE//10
    num_culc = num_sample * num_r
    Q = (0, 1, 10)
    s = random.sample(V, num_sample)
    r_samp = random.sample(V, num_r)
    ts = time.time()
    print("average time")
    print("Nbc 0 1 10")
    for i in range(12): #ビーコンの数
        avetime = {0:[], 1:[], 10:[]}
        for j in range(num_sample): #送金を行うノード候補のリストsのインデックス
            Beacon_Discovery(s[j], i, F)
            for r in r_samp:
                if s[j] != r:
                    for tab in Q:
                        t1 = time.time()
                        P, rr = Candicate_rotes(s[j], r, 5, 10, tab)
                        t2 = time.time()
                        avetime[tab].append(t2 - t1)
                        if len(P) != 0:
                            #for pi in P:
                            #    pathplot(pi, rr[pi])
                            accessible[tab][i] += 1
        avetime0 = sum(avetime[0])/len(avetime[0])
        avetime1 = sum(avetime[1])/len(avetime[1])
        avetime10 = sum(avetime[10])/len(avetime[10])
        print("{} {} {} {}".format(i, avetime0, avetime1, avetime10))

    te = time.time()
    print("Accessible")
    print("Nbc 0 1 10")
    for n in range(12):
        print("{} {} {} {}".format(n, accessible[0][n]/num_culc, accessible[1][n]/num_culc, accessible[10][n]/num_culc))
    #print("average_time = {}".format(avetime/(num_culc*12*3)))
    print("total_time = {}".format(te-ts))

def Simulation4(V, E, F):
    #時間による変化を導入する。
    #平均計算時間を求めない
    #時刻tにおいてパスを発見できた割合と時刻t-1からtになってパスが見つからなくなった割合、見つかるようになった割合をだす
    G = (V, E)
    num_sample = 10
    num_r = NUM_NODE//10
    num_culc = num_sample * num_r
    s = random.sample(V, num_sample)
    r_samp = random.sample(V, num_r)
    #accessible[(t, v, u)]:時刻tでノードuからvへの送金ができたかを記録する
    accessible = {t:{(v, u): 0 for v in s for u in r_samp} for t in range(60)}
    print("Accessible")
    print("t  %/100")
    find = 0
    disfind = 0
    for t in range(60):
        for j in range(num_sample): #送金を行うノード候補のリストsのインデックス
            Beacon_Discovery(s[j], 6, F)
            for r in r_samp:
                if s[j] != r:
                    P, rr = Candicate_rotes(s[j], r, 5, 10, 10)
                    if len(P) != 0:
                        #for pi in P:
                        #    pathplot(pi, rr[pi])
                        maxp = max(rr, key=rr.get)
                        s[j].path[r] = maxp
                        accessible[t][(s[j], r)] = 1
        ave = sum(accessible[t].values()) / len(accessible[t])
        if t > 0:
            for sr in accessible[t].keys():
                if accessible[t][sr] == 1 and accessible[t-1][sr] == 0:
                    find += 1
                elif accessible[t][sr] == 0 and accessible[t-1][sr] == 1:
                    disfind += 1
        print("{} {} {} {}".format(t, ave, find/num_culc, disfind/num_culc))
        LN_UPD(V, E, F)
        F1 = {k:1 for k in E}
        ts = time.time()
        for v in V:
            check_RT(v, F1)
        te = time.time()
        print("check_RT time: ", (te-ts)/len(V))


def connect(V, E):
    q = queue.Queue()
    F = [False for n in range(NUM_NODE)]
    F[0] = True
    q.put(V[0])
    while not all(F):
        v = q.get()
        for u in v.adj:
            if F[u.name] == False:
                F[u.name] = True
                q.put(u)
    if all(F):
        print("LN in connected")
    else:
        print("LN is disconnected")

if __name__ == "__main__":
    address = Generater()
    print("make network", end="")
    t1 = time.time()
    V, E, F = make_network()
    t2 = time.time()
    print(": {}[s]".format(t2-t1))
    for v in V:
        v.M = set()
        v.Mr = set()
    plotLN(V, E)
    print("simulation start")
    Simulation4(V, E, F)
    #plotLN(V, E)