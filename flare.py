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
import collections

MAX_CAP = 100
MIN_CAP = 10
NUM_NODE = 2000 #ネットワークのノードの数
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
        #self.new_address(bytes.fromhex("00"))

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
        self.num_TABLE_REQ = 0 #selfがRTを要求された回数。

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
                if each_hop < ahop and check_path(self.path[z]):
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
        
        if e[::-1] in self.RT:
            self.RT.remove(e[::-1])

    def Add(self, e, ncap, nfee, F):
        self.set_adj_edge(e)
        self.cap[e] = self.cap[e[::-1]] = ncap
        self.fee[e] = self.fee[e[::-1]] = F[e] = F[e[::-1]] = nfee
        self.M.add(e)
        u = list(e)
        u.remove(self)
        self.M = self.M & u[0].RT
    
    def Reset(self):
        #名前とアドレス以外を全て消す
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
        self.num_TABLE_REQ = 0 #selfがRTを要求された回数。0:グループあり 1:グループなし

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
    #パスpについて、使用しているノードが全てアクティブか、辺が繋がっていないはずの場所を通っていないか確認
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
    if len(u.adj) == 0:
        return
    new_bc = set()
    #もしu.bcが空でなかった場合、u.bcへのパスがちゃんと繋がっているかを確認
    while u.bc:
        v = u.bc.pop()
        if check_path(u.path[v]):
            new_bc.add(v)
        else:
            v.rb.remove(u)
    u.bc = new_bc
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
                #ここでRTにe,e[::-1]があるかどうか確認したほうがいい
                if e not in u.RT and e[::-1] not in u.RT:
                    u.RT.add(e)
                    u.fee[e] = u.fee[e[::-1]] = F[e]
                    u.cap[e] = u.cap[e[::-1]] = e[0].cap[e]
                if zpath[v][i+1] not in u.path.keys():
                    u.path[zpath[v][i+1]] = zpath[v][0:i+2]
                    u.dist[zpath[v][i+1]] = len(zpath[v][0:i+2])
            u.path[v] = zpath[v]
            u.dist[v] = len(zpath[v])
            v.rb.append(u)
    

def Candicate_rotes(s, r, k, f, Ntab):
    #送信者sから受信者rへの送金ルートをk本発見する
    #Ntab：ルーティングテーブルを要求するノードの最大数。Ntab個以上のノードにルーティングテーブルを要求しない
    #f：送金額。評価値の計算に使うかも
    #発見したパスの集合、評価値、クエリを送信した回数を返す
    RTco = s.RT
    P = set() #候補ルートを格納するリスト。重複を起こさないためsetにしている
    U = set() #ルーティングテーブルを取得した受信者に近いノードのリスト
    fee = dict()
    cap = dict()
    rr = dict() #パスpの評価値を格納する
    Mbar = set()

    #もしs-r間に既知のパスがあり、経由するノード全てがアクティブでチャネルが消えてないならそのパスをそのまま使う。
    pbar = set()
    if r in s.candicate.keys():
        for path in s.candicate[r]:
            if check_path(path):
                P.add(path)
                rr[path] = route_ranking(f, path)
            else:
                pbar.add(path)
        for rm_path in pbar:
            s.candicate[r].remove(rm_path)

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
        if len(beacon - U) == 0:
            break
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
    return P, rr, len(U)

def Candicate_rotes_G(s, r, k, f, Ntab):
    #送信者sから受信者rへの送金ルートをk本発見する
    #探索の際に各ノードが何回RTを要求されたのかを記録する
    #Ntab：ルーティングテーブルを要求するノードの最大数。Ntab個以上のノードにルーティングテーブルを要求しない
    #f：送金額。評価値の計算に使うかも
    #発見したパスの集合、評価値、クエリを送信した回数を返す
    RTco = s.RT
    P = set() #候補ルートを格納するリスト。重複を起こさないためsetにしている
    U = set() #ルーティングテーブルを取得した受信者に近いノードのリスト
    fee = dict()
    cap = dict()
    rr = dict() #パスpの評価値を格納する
    Mbar = set()

    #もしs-r間に既知のパスがあり、経由するノード全てがアクティブでチャネルが消えてないならそのパスをそのまま使う。
    pbar = set()
    if r in s.candicate.keys():
        for path in s.candicate[r]:
            if check_path(path):
                P.add(path)
                rr[path] = route_ranking(f, path)
            else:
                pbar.add(path)
        for rm_path in pbar:
            s.candicate[r].remove(rm_path)

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
        if len(beacon - U) == 0:
            break
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
            c.num_TABLE_REQ += 1
            U.add(c)
    #発見した候補ルートを記録
    #s.candicate[r] = P
    return P, rr, len(U)

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
        
def make_network(V):
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

    #print("|V|={}, |E|={}".format(len(V), len(Emiddle)))

    for v in range(NUM_NODE):
        for u in V[v].adj:
            RT_UPD(V[u.name], V[v], V[v].RT, {})
            if len(V[v].cap) != len(V[v].RT)*2:
                print("hoge")
    return V, Emiddle, F

def make_network2(V):
    #seed値を固定し、複数回実行しても同じグラフができるようにする
    knb = 4

    ###この構造体のイニシャライズは最初の1回だけにしないとダメ###
    #V = [Node(n) for n in range(NUM_NODE)]

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
    #ここでseed値を1回だけ初期化する
    random.seed(10)
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

def make_HaSnetwork():
    #ハブアンドスポークネットワークを作成する
    #まずノード数NUM_NODE/2のスモールワールドネットワークを2つ作成
    #その2つの間に辺をいくつか張ることで作成する
    knb = 4
    V = [Node(n) for n in range(NUM_NODE)]
    V1 = V[0:NUM_NODE//2]
    V2 = V[NUM_NODE//2:NUM_NODE]
    #ネットワークが円環状になるようにエッジを貼る
    E1 = [(V1[i], V1[i+1]) for i in range(len(V1)-1)]
    E2 = [(V2[i], V2[i+1]) for i in range(len(V2)-1)]
    E1.append((V1[-1], V1[0]))
    E2.append((V2[-1], V2[0]))
    F = {(i,j):math.inf for i in V1 for j in V1}
    F2 = {(i,j):math.inf for i in V2 for j in V2}

    #最近傍の数がknb個になるように近くのノードとエッジを貼る
    for i in range(NUM_NODE//2):
        for n in range(2,(knb//2)+1):
            E1.append((V1[i-n], V1[i]))
            E2.append((V2[i-n], V2[i]))

    Emiddle1 = copy.copy(E1) #張替え後のエッジを格納する
    #全ての辺について確率PROB_EDGEで張替える。
    for e in E1:
        if random.random() < PROB_EDGE:
            #貼り替える場合ランダムに頂点vを1つ選択し、辺(e[0],v)がすでに存在しなければ追加、元の辺を削除
            v = random.choice(V1)
            if e[0] != v and (e[0], v) not in Emiddle1 and (v, e[0]) not in Emiddle1:
                Emiddle1.remove(e)
                if e[0].name < v.name:
                    e = (e[0], v)
                else:
                    e = (v, e[0])
                Emiddle1.append(e)
        #エッジを張り替えるかの処理が終わったら、そのエッジは確定するので隣接とcap,feeを処理する
        e[0].set_adj_edge(e)
        e[1].set_adj_edge(e)
        e[0].cap[e] = e[0].cap[e[::-1]] = \
        e[1].cap[e] = e[1].cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
        e[0].fee[e] = e[0].fee[e[::-1]] = \
        e[1].fee[e] = e[1].fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)
    
    Emiddle2 = copy.copy(E2)
    for e in E2:
        if random.random() < PROB_EDGE:
            #貼り替える場合ランダムに頂点vを1つ選択し、辺(e[0],v)がすでに存在しなければ追加、元の辺を削除
            v = random.choice(V2)
            if e[0] != v and (e[0], v) not in Emiddle2 and (v, e[0]) not in Emiddle2:
                Emiddle2.remove(e)
                if e[0].name < v.name:
                    e = (e[0], v)
                else:
                    e = (v, e[0])
                Emiddle2.append(e)
        #エッジを張り替えるかの処理が終わったら、そのエッジは確定するので隣接とcap,feeを処理する
        e[0].set_adj_edge(e)
        e[1].set_adj_edge(e)
        e[0].cap[e] = e[0].cap[e[::-1]] = \
        e[1].cap[e] = e[1].cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
        e[0].fee[e] = e[0].fee[e[::-1]] = \
        e[1].fee[e] = e[1].fee[e[::-1]] = F2[e] = F2[e[::-1]] = random.randint(1, 10)

    Emiddle = Emiddle1 + Emiddle2
    V = V1+V2
    F.update(F2)

    vb1 = random.sample(V1, 1)
    vb2 = random.sample(V2, 1)

    while vb1 and vb2:
        e = (vb1.pop(), vb2.pop())
        Emiddle.append(e)
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

def make_Starnetwork():
    #星型のネットワークを作成
    #中心となるノードを1つ定め、全てのノードは中心とのみ隣接する
    V = [Node(n) for n in range(NUM_NODE)]
    E = []
    F = {(i,j):math.inf for i in V for j in V}
    center_node = V[NUM_NODE//2]

    for v in V:
        if v != center_node:
            if v.name < center_node.name:
                e = (v, center_node)
            else:
                e = (center_node, v)
            E.append(e)
            #エッジを張り替えるかの処理が終わったら、そのエッジは確定するので隣接とcap,feeを処理する
            e[0].set_adj_edge(e)
            e[1].set_adj_edge(e)
            e[0].cap[e] = e[0].cap[e[::-1]] = \
            e[1].cap[e] = e[1].cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
            e[0].fee[e] = e[0].fee[e[::-1]] = \
            e[1].fee[e] = e[1].fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)
    
    print("|V|={}, |E|={}".format(len(V), len(E)))

    for v in range(NUM_NODE):
        for u in V[v].adj:
            RT_UPD(V[u.name], V[v], V[v].RT, {})
            if len(V[v].cap) != len(V[v].RT)*2:
                print("hoge")
    return V, E, F
            

def LN_UPD(V, E, F):
    #LNを更新する。V：更新前のLNの頂点集合 E：辺集合 F：重みの集合
    Eadd = 10
    Vadd = 0
    Edel = 10 #追加、削除する辺、頂点の数
    Vdel = 0
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
            ebar.append(e)
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
            E.append(e)
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
            E.append(e)
            cap = random.randint(MIN_CAP, MAX_CAP)
            fee = random.randint(1, 10)
            e[0].Add(e, cap, fee, F)
            e[1].Add(e, cap, fee, F)
            Vupd.add(u)
            Vupd.add(v)
            NEIGHBOR_UPD(Vupd)
        add_num += 1
    print("")
        
def RT_remake(V, E, F, Egroup):
    #LNを更新する。V：更新前のLNの頂点集合 E：辺集合 F：重みの集合
    Eadd = 10
    Vadd = 0
    Edel = 10 #追加、削除する辺、頂点の数
    Vdel = 0
    Vgroup = Nodes(Egroup)

    #辺の集合Eの中で消していいものだけを残した集合Efreeを作る、Egroupの辺は消してはいけない
    Efree = set(E) - set(Egroup)
    Vfree = set(V) - set(Vgroup)
    ebar = random.sample(Efree, Edel)
    vbar = random.sample(Vfree, Vdel)

    for v in V:
        v.RT = set()

    for j in range(len(ebar)):
        e = ebar[j]
        E.remove(e)
        e[0].adj.remove(e[1])
        e[1].adj.remove(e[0])

    #ノードをノンアクティブにする
    for v in vbar:
        for u in v.adj:
            v.active = 0
            e = (v, u)
            E.remove(e)
            ebar.append(e)
            u.adj.remove(v)

    #辺、ノードを消したら、RTに辺を追加する
    for v in V:
        for u in v.adj:
            if v.name < u.name:
                e = (v,u)
            else:
                e = (u,v)
            v.RT.add(e)

    #新しいチャネルを追加    
    add_num = 0
    while add_num < Eadd:
        e = tuple(random.sample(V, 2))
        if e not in E and e[::-1] not in E:
            E.append(e)
            e[0].cap[e] = e[0].cap[e[::-1]] = \
            e[1].cap[e] = e[1].cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
            e[0].fee[e] = e[0].fee[e[::-1]] = \
            e[1].fee[e] = e[1].fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)
            e[0].set_adj_edge(e)
            e[1].set_adj_edge(e)
            add_num += 1

    #新しいノードを追加
    add_num = 0
    lenV = len(V)
    while add_num < Vadd:
        adj = random.sample(V, 4)
        v = Node(lenV + add_num + 1)
        V.append(v)
        for u in adj:
            e = (u, v)
            E.append(e)
            u.set_adj_edge(e)
            v.set_adj_edge(e)
            u.cap[e] = u.cap[e[::-1]] = \
            v.cap[e] = v.cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
            u.fee[e] = u.fee[e[::-1]] = \
            v.fee[e] = v.fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)
        add_num += 1

    for v in range(NUM_NODE):
        for u in V[v].adj:
            RT_UPD(V[u.name], V[v], V[v].RT, {})

def Remake_for_logs(V, E, F, Egroup, ebar, enew):
    #LNを更新する。V：更新前のLNの頂点集合 E：辺集合 F：重みの集合
    Eadd = 10
    Vadd = 0
    Edel = 10 #追加、削除する辺、頂点の数
    Vdel = 0
    Vgroup = Nodes(Egroup)

    #辺の集合Eの中で消していいものだけを残した集合Efreeを作る、Egroupの辺は消してはいけない
    Efree = set(E) - set(Egroup)
    Vfree = set(V) - set(Vgroup)
    vbar = []
    if len(ebar) == 0:
        ebar = random.sample(Efree, Edel)
        vbar = random.sample(Vfree, Vdel)
    if len(enew) == 0:
        while len(enew) < Eadd:
            e = tuple(random.sample(V, 2))
            if e not in E and e[::-1] not in E and e not in enew and e[::-1] not in enew:
                enew.append(e)

    for v in V:
        v.RT = set()

    for j in range(len(ebar)):
        e = ebar[j]
        if e not in Egroup:
            E.remove(e)
            e[0].adj.remove(e[1])
            e[1].adj.remove(e[0])

    #ノードをノンアクティブにする
    for v in vbar:
        for u in v.adj:
            v.active = 0
            e = (v, u)
            E.remove(e)
            ebar.append(e)
            u.adj.remove(v)

    #辺、ノードを消したら、RTに辺を追加する
    for v in V:
        for u in v.adj:
            if v.name < u.name:
                e = (v,u)
            else:
                e = (u,v)
            v.RT.add(e)

    random.seed(100)
    #新しいチャネルを追加    
    for e in enew:
        E.append(e)
        e[0].cap[e] = e[0].cap[e[::-1]] = \
        e[1].cap[e] = e[1].cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
        e[0].fee[e] = e[0].fee[e[::-1]] = \
        e[1].fee[e] = e[1].fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)
        e[0].set_adj_edge(e)
        e[1].set_adj_edge(e)

    #新しいノードを追加
    add_num = 0
    lenV = len(V)
    while add_num < Vadd:
        adj = random.sample(V, 4)
        v = Node(lenV + add_num + 1)
        V.append(v)
        for u in adj:
            e = (u, v)
            E.append(e)
            u.set_adj_edge(e)
            v.set_adj_edge(e)
            u.cap[e] = u.cap[e[::-1]] = \
            v.cap[e] = v.cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
            u.fee[e] = u.fee[e[::-1]] = \
            v.fee[e] = v.fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)
        add_num += 1

    for v in range(NUM_NODE):
        for u in V[v].adj:
            RT_UPD(V[u.name], V[v], V[v].RT, {})

    return ebar, enew

def make_group(V, E, F, frequent_canel, num_member):
    #頻出チャネルの情報からユーザーグループを作成する。3人~10人くらい

    #まずfrequent_chanelから候補ユーザーを特定する。
    #候補ノードはそのノードをビーコンとして選択しているノードの数rbでソートしておく
    frequent_node = Nodes(frequent_canel)
    ranked_node = []
    while frequent_node:
        u = frequent_node.pop()
        index = 0
        while index < len(ranked_node):
            if len(u.rb) < len(ranked_node[index].rb):
                break
            index += 1
        ranked_node.insert(index, u)

    #ソートした候補の中で先頭num_mamber個までをグループのメンバーにする
    Emember = ranked_node[0:num_member]
    Egroup = [(i, j) for i in Emember for j in Emember if i.name < j.name]

    ebar = set()
    for e in Egroup:
        if e not in E:
            E.append(e)
            ebar.add(e)
            e[0].cap[e] = e[0].cap[e[::-1]] = \
            e[1].cap[e] = e[1].cap[e[::-1]] = random.randint(MIN_CAP, MAX_CAP)
            e[0].fee[e] = e[0].fee[e[::-1]] = \
            e[1].fee[e] = e[1].fee[e[::-1]] = F[e] = F[e[::-1]] = random.randint(1, 10)
            e[0].set_adj_edge(e)
            e[1].set_adj_edge(e)
    
    return Egroup, ebar

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
            
def count_chanel_used(p, num_canel_used):
    #パスpの中で使用しているチャネルを確認し、その使用数をカウントする
    i = 0
    while i < len(p)-1:
        if p[i].name < p[i+1].name:
            e = (p[i], p[i+1])
        else:
            e = (p[i+1], p[i])
        
        if e in num_canel_used.keys():
            num_canel_used[e] += 1
        else:
            num_canel_used[e] = 1
        i += 1            

def num_TABLE_REQ_reset(V):
    i = 0
    while i < NUM_NODE:
        V[i].num_TABLE_REQ = 0
        i += 1 

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
                        P, rr, q = Candicate_rotes(s[j], r, 5, 10, tab)
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

def Simulation1B(V, E, F):
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
                        P, rr, q = Candicate_rotes(s[j], r, 5, 10, 10)
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

def Simulation2(V, E, F):
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
                        P, rr, q = Candicate_rotes(s[j], r, 5, 10, tab)
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

def Simulation3(V, E, F):
    #時間による変化を導入する。
    #平均計算時間を求めない
    #時刻tにおいてパスを発見できた割合と時刻t-1からtになってパスが見つからなくなった割合、見つかるようになった割合をだす
    num_sample = 10
    num_r = NUM_NODE//10
    s = random.sample(V, num_sample)
    r_samp = random.sample(V, num_r)
    #accessible[(t, v, u)]:時刻tでノードuからvへの送金ができたかを記録する
    accessible = {t:{(v, u): 0 for v in s for u in r_samp} for t in range(30)}
    print("Accessible")
    print("t  %/100")
    find = 0
    disfind = 0
    access = 0
    disaccess = 0
    for t in range(30):
        for j in range(num_sample): #送金を行うノード候補のリストsのインデックス
            Beacon_Discovery(s[j], 6, F)
            for r in r_samp:
                if s[j] != r:
                    ###Candicate_routes(s, r, k, f, Ntab)において、Ntab<NUM_NODEにしないといけない
                    P, rr, q = Candicate_rotes(s[j], r, 5, 10, 10)
                    if len(P) != 0:
                        #for pi in P:
                        #    pathplot(pi, rr[pi])
                        maxp = max(rr, key=rr.get)
                        s[j].path[r] = maxp
                        accessible[t][(s[j], r)] = 1
        ave = sum(accessible[t].values()) / len(accessible[t])
        c = collections.Counter(accessible[t].values())
        access += c[1]
        disaccess += c[0]
        if t > 0:
            for sr in accessible[t].keys():
                if accessible[t][sr] == 1 and accessible[t-1][sr] == 0:
                    find += 1
                elif accessible[t][sr] == 0 and accessible[t-1][sr] == 1:
                    disfind += 1
        print("{} {}".format(t, ave))
        ts = time.time()
        RT_remake(V, E, F, [])
        te = time.time()
        print("RT_remake time: ", te-ts)
        F1 = {}
        for k in E:
            F1[k] = 1
            F1[k[::-1]] = 1
        ts = time.time()
        for v in V:
            check_RT(v, F1)
        te = time.time()
        print("check_RT time: ", (te-ts)/len(V))
    print("access %, disaccess %")
    print(find/access, ", ", disfind/disaccess)

def Simulation4(V, E, F):
    #実験4　少数ユーザーのグループを作ることでパスを発見しやすくなるか
    #パスの発見確率だけでなく、発見するまでのクエリの回数を比較
    #クエリの回数が少ない=より早く見つかっている
    #ユーザグループの作り方を色々試す
    T = 600
    num_sample = 10
    num_r = NUM_NODE//10
    s = random.sample(V, num_sample)
    r_samp = random.sample(V, num_r)
    num_culc = 0
    #accessible[(t, v, u)]:時刻tでノードuからvへの送金ができたかを記録する
    accessible = {t:{(v, u): 0 for v in s for u in r_samp if v != u} for t in range(T)}
    num_query = {t: 0 for t in range(T)} #時刻tでの探索においてクエリを送信した回数の合計
    num_chanel_used = {}
    print("Accessible, ave_query, TABLE_REQ")
    print("t          not_group              group  ")
    find = 0
    disfind = 0
    access = 0
    disaccess = 0
    #少数ユーザーのグループを繋ぐ辺の集合。これは消してはいけない
    Egroup = list()
    for t in range(30):
        for j in range(num_sample): #送金を行うノード候補のリストsのインデックス
            Beacon_Discovery(s[j], 6, F)
            for r in r_samp:
                if s[j] != r:
                    ###Candicate_routes(s, r, k, f, Ntab)において、Ntab<NUM_NODEにしないといけない
                    P, rr, q = Candicate_rotes(s[j], r, 5, 10, 10)
                    num_query[t] += q
                    num_culc += 1
                    if len(P) != 0:
                        for pi in P:
                            count_chanel_used(pi, num_chanel_used)
                        maxp = max(rr, key=rr.get)
                        s[j].path[r] = maxp
                        accessible[t][(s[j], r)] = 1
                    num_TABLE_REQ_reset(V)
        ave = sum(accessible[t].values()) / len(accessible[t])
        c = collections.Counter(accessible[t].values())
        access += c[1]
        disaccess += c[0]
        if t > 0:
            for sr in accessible[t].keys():
                if accessible[t][sr] == 1 and accessible[t-1][sr] == 0:
                    find += 1
                elif accessible[t][sr] == 0 and accessible[t-1][sr] == 1:
                    disfind += 1
        print("{} {} {}".format(t, ave, num_query[t]/num_culc ) )
        RT_remake(V, E, F, Egroup)
        F1 = {}
        for k in E:
            F1[k] = 1
            F1[k[::-1]] = 1
        for v in V:
            check_RT(v, F1)
    print("access %, disaccess %")
    print(find/access, ", ", disfind/disaccess)

    
    print("後半開始")
    #チャネルの使用回数でnum_chanel_usedをソートし、その先頭10個くらいをfrequent_chanelにする
    #ここから計算の手間を比較するためにEgroupを作る場合と作らない場合に分ける
    #作らない場合：V,E,Fを使う
    #使う場合：Vg,Eg,Fgを使う)
    num_chanel_used_sorted = sorted(num_chanel_used.items(), key=lambda x: x[1])
    frequent_canel = [row[0] for row in num_chanel_used_sorted[0:10]]
    Egroup, ebar = make_group(V, E, F, frequent_canel, 3)
    group_member = Nodes(Egroup)
    RT_remake(V, E, F, Egroup)
    F1 = {}
    for k in E:
        F1[k] = 1
        F1[k[::-1]] = 1
    for v in V:
        check_RT(v, F1)

    #グループ作成後の各記録を保存する変数を作成
    num_queryG = {}
    accessibleG = {}
    accessibleG[30 - 1] = accessible[30 -1]
    accessG = access
    disaccessG = disaccess
    findG = find
    disfindG = disfind
    for t in range(30,T):
        num_queryG[t] = 0
        accessibleG[t] = {}
        sum_TABEL_REQ = [0, 0]
        for j in range(num_sample): #送金を行うノード候補のリストsのインデックス
            Beacon_Discovery(s[j], 6, F)
            for r in r_samp:
                if s[j] != r:
                    ###Candicate_routes(s, r, k, f, Ntab)において、Ntab<NUM_NODEにしないといけない
                    P, rr, q = Candicate_rotes_G(s[j], r, 5, 10, 10)
                    num_query[t] += q
                    num_culc += 1
                    if len(P) != 0:
                        accessible[t][(s[j], r)] = 1
                    
                    accessibleG[t][(s[j], r)] = 0
                    P, rr, q = Candicate_rotes(s[j], r, 5, 10, 10)
                    num_queryG[t] += q
                    if len(P) != 0:
                        maxp = max(rr, key=rr.get)
                        s[j].path[r] = maxp
                        accessibleG[t][(s[j], r)] = 1
        for v in group_member:
            sum_TABEL_REQ[0] += v.num_TABLE_REQ[0]
            sum_TABEL_REQ[1] += v.num_TABLE_REQ[1]
        num_TABLE_REQ_reset(V)
        ave = sum(accessible[t].values()) / len(accessible[t])
        c = collections.Counter(accessible[t].values())
        access += c[1]
        disaccess += c[0]
        if t > 0:
            for sr in accessible[t].keys():
                if accessible[t][sr] == 1 and accessible[t-1][sr] == 0:
                    find += 1
                elif accessible[t][sr] == 0 and accessible[t-1][sr] == 1:
                    disfind += 1
        aveG = sum(accessibleG[t].values()) / len(accessibleG[t])
        c = collections.Counter(accessibleG[t].values())
        accessG += c[1]
        disaccessG += c[0]
        if t > 0:
            for sr in accessibleG[t].keys():
                if accessibleG[t][sr] == 1 and accessibleG[t-1][sr] == 0:
                    findG += 1
                elif accessibleG[t][sr] == 0 and accessibleG[t-1][sr] == 1:
                    disfindG += 1
        print("{} {} {} {} | {} {} {}".format(t, ave, num_query[t]/num_culc, sum_TABEL_REQ[1], aveG, num_queryG[t]/num_culc, sum_TABEL_REQ[0]))
        RT_remake(V, E, F, Egroup)
        F1 = {}
        for k in E:
            F1[k] = 1
            F1[k[::-1]] = 1
        for v in V:
            check_RT(v, F1)
    print("access %, disaccess %, accessG %, disaccessG %")
    print(find/access, ", ", disfind/disaccess, "," , findG/accessG,",", disfindG/disaccessG)

def Simulation4B():
    #実験4B　グループの人数を変えながら実験する
    #パスの発見確率だけでなく、発見するまでのクエリの回数を比較
    #クエリの回数が少ない=より早く見つかっている
    #ユーザグループの作り方を色々試す
    T = 60
    num_sample = 10
    num_r = NUM_NODE//10
    NUM_Member = [0,5,10,15,20,25,30,35,40,45,50]
    #LNの更新履歴を保存する変数。ebar[t]:時刻tで消える辺 enew[t]:時刻tで増える辺
    ebar = {t: [] for t in range(T)}
    enew = {t: [] for t in range(T)}
    V = [Node(n) for n in range(NUM_NODE)]
    while NUM_Member:
        strings = []
        group_member = []
        #ここでグラフを作る。
        #メンバーの人数が変わるたびにグラフを初期化し、変更履歴に基づき同じように更新することで同一のグラフで実験する
        strings.append("|M| = {}".format(NUM_Member[0]))
        print(strings[-1])
        strings.append("make network |V|={} |E|={}".format(NUM_NODE, NUM_NODE*2))
        print(strings[-1])
        V, E, F = make_network2(V)
        #plotLN(V, E)
        for v in V:
            v.M = set()
            v.Mr = set()

        s = random.sample(V, num_sample)
        r_samp = random.sample(V, num_r)
        num_culc = 0
        #accessible[(t, v, u)]:時刻tでノードuからvへの送金ができたかを記録する
        accessible = {t:{(v, u): 0 for v in s for u in r_samp if v != u} for t in range(T)}
        num_query = {t: 0 for t in range(T)} #時刻tでの探索においてクエリを送信した回数の合計
        num_chanel_used = {}
        strings.append("                not_group                          group  ")
        print(strings[-1])
        strings.append("t, Accessible, ave_query, ave_time, TABLE_REQ")
        print(strings[-1])
        find = 0
        disfind = 0
        access = 0
        disaccess = 0
        #少数ユーザーのグループを繋ぐ辺の集合。これは消してはいけない
        Egroup = list()
        Member = NUM_Member.pop(0)
        for t in range(T):
            sumtime_t = 0
            sum_TABEL_REQ = 0
            for j in range(num_sample): #送金を行うノード候補のリストsのインデックス
                Beacon_Discovery(s[j], 6, F)
                for r in r_samp:
                    if s[j] != r:
                        ###Candicate_routes(s, r, k, f, Ntab)において、Ntab<NUM_NODEにしないといけない
                        t1 = time.time()
                        P, rr, q = Candicate_rotes_G(s[j], r, 5, 10, 10)
                        t2 = time.time()
                        sumtime_t += t2-t1
                        num_query[t] += q
                        num_culc += 1
                        if len(P) != 0:
                            for pi in P:
                                count_chanel_used(pi, num_chanel_used)
                            maxp = max(rr, key=rr.get)
                            s[j].path[r] = maxp
                            accessible[t][(s[j], r)] = 1
            for v in group_member:
                sum_TABEL_REQ += v.num_TABLE_REQ
            num_TABLE_REQ_reset(V)
            if Member == 0:
                ave_TABLE_REQ = 0
            else:
                ave_TABLE_REQ = sum_TABEL_REQ/Member
            ave = sum(accessible[t].values()) / len(accessible[t])
            c = collections.Counter(accessible[t].values())
            access += c[1]
            disaccess += c[0]
            if t > 0:
                for sr in accessible[t].keys():
                    if accessible[t][sr] == 1 and accessible[t-1][sr] == 0:
                        find += 1
                    elif accessible[t][sr] == 0 and accessible[t-1][sr] == 1:
                        disfind += 1
            strings.append('{:0=2} {:.10f} {:.10f} {:.10f} {:.8f}'.format(t, ave, num_query[t]/num_culc,\
                sumtime_t/num_culc, ave_TABLE_REQ))
            print(strings[-1])

            #t=29まで探索を終えたらグループを作成する
            if t == 29:
                #チャネルの使用回数でnum_chanel_usedをソートし、その先頭10個くらいをfrequent_chanelにする
                num_chanel_used_sorted = sorted(num_chanel_used.items(), key=lambda x: x[1])
                frequent_canel = [row[0] for row in num_chanel_used_sorted]
                Egroup, Gedge = make_group(V, E, F, frequent_canel, Member)
                group_member = Nodes(Egroup)
            
            ebar[t], enew[t] = Remake_for_logs(V, E, F, Egroup, ebar[t], enew[t])
            F1 = {}
            for k in E:
                F1[k] = 1
                F1[k[::-1]] = 1
            for v in V:
                check_RT(v, F1)
        if disaccess == 0:
            disaccess = 1
        strings.append("access %, disaccess %")
        print(strings[-1])
        strings.append("{}, {}".format(find/access, disfind/disaccess))
        print(strings[-1])

        #次の反復の準備としてVのアドレス以外の情報を削除する
        for v in V:
            v.Reset()
        with open("jikkenNumMem3.txt", "a", encoding="utf-8") as f:
            f.write("\n".join(strings))
            f.write("\n")



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
    #print("make network", end="")
    #t1 = time.time()
    #V = [Node(n) for n in range(NUM_NODE)]
    #V, E, F = make_network2(V)
    #t2 = time.time()
    #print(": {}[s]".format(t2-t1))
    #for v in V:
    #    v.M = set()
    #    v.Mr = set()
    #plotLN(V, E)
    print("simulation start")
    Simulation4B()
    #plotLN(V, E)