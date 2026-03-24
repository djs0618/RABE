'''
Contains all the auxillary functions to do linear secret sharing (LSS) over an access structure. Mainly, we represent the 
access structure as a binary tree. This could also support matrices for representing access structures.
'''
#实现线性秘密共享和访问结构的处理，通过将策略表示为二叉树，可以灵活地进行秘密共享和恢复操作。它支持复杂的访问策略，并提供了多种辅助方法来操作和评估策略树。


from charm.core.math.pairing import ZR
from policytree import *

class SecretUtil:
    #初始化时接收一个群对象groupObj，用于后续的数学运算。
    def __init__(self, groupObj, verbose=True):
        self.group = groupObj        
#        self.parser = PolicyParser()

    #定义方法P，计算多项式在点x处的值，用于秘密共享。
    def P(self, coeff, x):
        share = 0
        # evaluate polynomial计算多项式
        for i in range(0, len(coeff)):
            share += (coeff[i] * (x ** i))
        return share

    #使用多项式插值方法将秘密secret分割成n个份额，其中至少需要k个份额才能恢复秘密。
    def genShares(self, secret, k, n):
        if(k <= n):#F(x)=secret+a1*x^1+a2*x^2+...+ak*x^k-1.
            rand = self.group.random
            a = [] # will hold polynomial coefficients将保存多项式系数
            for i in range(0, k):
                if (i == 0): a.append(secret) # a[0]
                else: a.append(rand(ZR))
            Pfunc = self.P 
            shares = [Pfunc(a, i) for i in range(0, n+1)]
        return shares
    
    # shares is a dictionary
    #使用拉格朗日插值法恢复多项式的系数(a1、a2、...、ak)。
    def recoverCoefficients(self, list):
        """recovers the coefficients over a binary tree."""#恢复二叉树上的系数
        coeff = {}
        list2 = [self.group.init(ZR, i) for i in list] # 将整数转换为群元素
        for i in list2:
            result = 1
            for j in list2:
                if not (i == j):
                    # lagrange basis poly拉格朗日基多边形
                    result *= (0 - j) / (i - j)# 拉格朗日基多项式在x=0处的值.
#                #print("coeff '%d' => '%s'" % (i, result))
            coeff[int(i)] = result
        return coeff
        
    #根据共享字典恢复原始秘密。
    def recoverSecret(self, shares):
        """take shares and attempt to recover secret by taking sum of coeff * share for all shares.
        if user indeed has at least k of n shares, then secret will be recovered."""
        list = shares.keys()
        #if self.verbose: print(list)
        coeff = self.recoverCoefficients(list)
        secret = 0
        for i in list:
            secret += (coeff[i] * shares[i])

        return secret

    #获取策略树的系数。
    def getCoefficients(self, tree):
        coeffs = {}
        self._getCoefficientsDict(tree, coeffs)
        return coeffs
    
    #递归地获取策略树中各节点的系数。
    #AND节点：使用2个点（1,2）计算拉格朗日系数，左右子树分别乘不同系数。
    #OR节点：使用1个点（1）计算拉格朗日系数，左右子树分别乘相同系数。
    #ATTR节点：记录属性和系数。
    def _getCoefficientsDict(self, tree, coeff_list, coeff=1):
        """recover coefficient over a binary tree where possible node types are OR = (1 of 2)
        and AND = (2 of 2) secret sharing. The leaf nodes are attributes and the coefficients are
        recorded in a coeff-list dictionary.""" 
        if tree:
            node = tree.getNodeType()
            if(node == OpType.AND):
                this_coeff = self.recoverCoefficients([1,2])
                # left child => coeff[1], right child => coeff[2]
                self._getCoefficientsDict(tree.getLeft(), coeff_list, coeff * this_coeff[1])
                self._getCoefficientsDict(tree.getRight(), coeff_list, coeff * this_coeff[2])
            elif(node == OpType.OR):
                this_coeff = self.recoverCoefficients([1])
                self._getCoefficientsDict(tree.getLeft(), coeff_list, coeff * this_coeff[1])
                self._getCoefficientsDict(tree.getRight(), coeff_list, coeff * this_coeff[1])
            elif(node == OpType.ATTR):
                attr = tree.getAttributeAndIndex()
                coeff_list[ attr ] = coeff
            else:
                return None
            
    #根据策略树计算秘密共享，返回列表或字典形式。
    def _calculateShares(self, secret, tree, _type=dict):
        """performs secret sharing over a policy tree. could be adapted for LSSS matrices."""
        attr_list = []
        self._compute_shares(secret, tree, attr_list)
        if _type == list:
            return attr_list
        else: # assume dict
            share = {}
            for i in range(0, len(attr_list)):
                key = attr_list[i][0].getAttributeAndIndex()
                if not key in share.keys():
                    share[ key ] = attr_list[i][1]
            return share
    
    #返回共享的列表形式的秘密共享结果。
    def calculateSharesList(self, secret, tree):
        """calculate shares from given secret and returns a list of shares."""        
        return self._calculateShares(secret, tree, list)
    
    #返回共享的字典形式的秘密共享结果。
    def calculateSharesDict(self, secret, tree):
        """calculate shares from given secret and returns a dict as {attribute:shares} pairs"""        
        return self._calculateShares(secret, tree, dict)
    
    #递归地在策略树上进行秘密共享。
    #AND节点（k=2）：生成2个份额 shares[1]（左子树） 和 shares[2]（右子树）
    #OR节点（k=1）：生成1个份额 shares[1]==shares[2]（左右子分配同一份额）
    def _compute_shares(self, secret, subtree, List):
        """computes recursive secret sharing over the binary tree. Start by splitting 1-of-2 (OR) or 2-of-2 (AND nodes).
         Continues recursively down the tree doing a round of secret sharing at each boolean node type."""
        k = 0
        if(subtree == None):
            return None
        
        type = subtree.getNodeType()
        if(type == OpType.ATTR):
            # visiting a leaf node
#            t = (subtree.getAttribute(), secret)
            t = (subtree, secret)
            List.append(t) # 属性节点直接记录份额
            return None
        elif(type == OpType.OR or type == OpType.AND):
            k = subtree.threshold # 1-of-2 or 2-of-2 # AND为2，OR为1
#        elif(type == OpType.AND):
#            k = 2 # 2-of-2
        else:
            return None
        # generate shares for k and n        
        shares = self.genShares(secret, k, n=2)
        # recursively generate shares for children nodes
        self._compute_shares(shares[1], subtree.getLeft(), List)
        self._compute_shares(shares[2], subtree.getRight(), List)
    
    #标准化属性名称，处理重复属性的索引。
    def strip_index(self, node_str):
        if node_str.find('_') != -1: return node_str.split('_')[0]
        return node_str
        
    # Added by Z. Wan 5/12/2015
    #剥离关键词列表中的值部分，仅保留关键词名=提取属性名（如 "role:admin" → "role"）。
    def keywords_strip(self, keyword_list):
        list_stripped = []
        for kw in keyword_list:
            if kw.find(':') != -1: list_stripped.append(kw.split(':')[0])
        return list_stripped 
    ################################
        
    
    #将策略字符串解析为策略树对象，策略 (A AND A) 转换为 (A_1 AND A_2)。。
    def createPolicy(self, policy_string):
        assert type(policy_string) == str, "invalid type for policy_string"
        #print("1")
        parser = PolicyParser()        
        #print("2", policy_string)
        policy_obj = parser.parse(policy_string)
        #print("3")
        _dictCount, _dictLabel = {}, {}
        parser.findDuplicates(policy_obj, _dictCount)
        #print("4")
        for i in _dictCount.keys(): 
            if _dictCount[ i ] > 1: _dictLabel[ i ] = 0
        parser.labelDuplicates(policy_obj, _dictLabel)
        return policy_obj
        
    #根据属性列表修剪策略树，返回满足策略所需的最小属性集合，例如属性 [A, B]对策略 (A AND B) OR C 剪枝后保留左子树。。
    def prune(self, policy, attributes, _search=0):
        """determine whether a given set of attributes satisfies the policy"""
        parser = PolicyParser()        
        return parser.prune(policy, attributes, _search)

    #按左到右顺序收集策略树中的所有属性。
    #获取策略树中的所有属性列表。
    def getAttributeList(self, Node):
        aList = []
        self._getAttributeList(Node, aList)
        return aList
    #递归地获取策略树中的属性列表。
    def _getAttributeList(self, Node, List):
        """retrieve the attributes that occur in a policy tree in order (left to right)"""
        if(Node == None):
            return None
        # V, L, R
        if(Node.getNodeType() == OpType.ATTR):
            List.append(Node.getAttributeAndIndex()) # .getAttribute()
        else:
            self._getAttributeList(Node.getLeft(), List)
            self._getAttributeList(Node.getRight(), List)
        return None

# TODO: add test cases here for SecretUtil

#创建SecretUtil实例，定义策略字符串，解析为策略树对象并进行测试。
#1、创建策略树：根节点为OR，左右子树为AND。2、递归分割秘密，生成四个属性的份额。3、满足左AND或右AND即可恢复密钥。
if __name__ == "__main__":
    util = SecretUtil(ZR)
    #keywords_list = ['abc:123', 'def:456', 'ghi:789']
    #list_stripped = util.keywords_strip(keywords_list)
    
    kw_policy = '(1001:1 and 1002:3) or (1003:3 and 1004:4)'
    kw_policy = util.createPolicy(kw_policy) 
    
    #print(kw_policy, type(kw_policy))
    #print(list_stripped)
    #print(keywords_list)
    #pass

