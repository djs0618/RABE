from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
from charm.toolbox.ABEnc import ABEnc
from Msp import MSP
from charm.toolbox.zknode import BinNode

debug = False

1
class FABECPABE(ABEnc):
    def __init__(self, group_obj, verbose=False):
        ABEnc.__init__(self)
        self.name = "FABEO CP-ABE"
        self.group = group_obj
        self.util = MSP(self.group, verbose)

    def setup(self):
        """生成公钥和主密钥"""
        if debug:
            print('\nSetup算法:\n')

        # 生成群元素
        g = self.group.random(G1)
        h = self.group.random(G2)
        e_gh = pair(g, h)

        alpha = self.group.random(ZR)

        # 计算公钥参数
        e_gh_alpha = e_gh ** alpha

        # 主密钥和公钥
        msk = {'alpha': alpha}
        pk = {'g': g, 'h': h, 'e_gh_alpha': e_gh_alpha}

        return pk, msk

    def keygen(self, pk, msk, attr_list, U, b):
        """生成密钥，b=0或1表示两个不同分支"""
        if debug:
            print('\nKeyGen算法:\n')

        r = self.group.random(ZR)

        # 计算H(|U|+1)
        zr_plus_1 = self.group.order() + 1
        b_hash = self.group.hash(str(zr_plus_1), G1)

        # 生成用户专属参数a_U
        a_U = self.group.hash(U, ZR)

        g = pk['g']
        alpha = msk['alpha']

        # 根据分支b生成不同的主密钥组件
        if b == 0:
            sk2 = (g ** a_U) * (b_hash ** r)
        else:
            sk2 = (g ** (alpha - a_U)) * (b_hash ** r)

        # 属性相关密钥组件
        sk1 = {}
        for attr in attr_list:
            attr_hash = self.group.hash(attr, G1)
            sk1[attr] = attr_hash ** r

        # 通用组件h^r
        h_r = pk['h'] ** r

        return {'attr_list': attr_list, 'h_r': h_r, 'sk1': sk1, 'sk2': sk2}

    def encrypt(self, pk, msg, policy_str):
        """加密消息"""
        if debug:
            print('\nEncrypt算法:\n')

        # 解析访问策略
        policy = self.util.createPolicy(policy_str)
        mono_span_prog = self.util.convert_policy_to_msp(policy)
        num_cols = self.util.len_longest_row

        # 选择随机数
        s0 = self.group.random(ZR)  # 对应原方案中的s1
        s1 = self.group.random(ZR)

        # 生成随机份额
        v = [s0]
        for i in range(num_cols - 1):
            v.append(self.group.random(ZR))

        # 计算H(|U|+1)
        b_hash = self.group.hash(str(self.group.order() + 1), G1)

        # 构建密文组件
        ct = {}
        for attr, row in mono_span_prog.items():
            attr_stripped = self.util.strip_index(attr)
            attr_hash = self.group.hash(attr_stripped, G1)
            len_row = len(row)

            # 计算M_i * v
            miv = sum(i[0] * i[1] for i in zip(row, v[:len_row]))
            ct[attr] = (b_hash ** miv) * (attr_hash ** s1)

        # 计算g2^s和g2^s'
        g_s0 = pk['h'] ** s0
        h_s1 = pk['h'] ** s1

        # 计算e(g, h)^(alpha*s) * m
        Cp = (pk['e_gh_alpha'] ** s0) * msg

        return {'policy': policy, 'g_s0': g_s0, 'h_s1': h_s1, 'ct': ct, 'Cp': Cp}

    def decrypt(self, pk, ctxt, sk0, sk1):
        """
        解密算法，使用两个分段密钥 sk0 和 sk1 解密密文
        """
        if debug:
            print('\nDecryption algorithm:\n')

        # 检查 sk0 的属性是否满足访问策略
        tree = ctxt['policy'] # BinNode(ctxt['policy'])
        nodes_sk0 = self.util.prune(tree, sk0['attr_list'])
        if not nodes_sk0:
            print("sk0 的属性不满足访问策略.")
            return None

        # 检查 sk1 的属性是否满足访问策略
        nodes_sk1 = self.util.prune(tree, sk1['attr_list'])
        if not nodes_sk1:
            print("sk1 的属性不满足访问策略.")
            return None

        # 计算 sk0 相关的乘积项
        prod_sk0 = 1
        prod_ct_sk0 = 1
        for node in nodes_sk0:
            attr = node.getAttributeAndIndex()
            attr_stripped = self.util.strip_index(attr)
            prod_sk0 *= sk0['sk1'][attr_stripped]
            prod_ct_sk0 *= ctxt['ct'][attr]

        # 计算 sk1 相关的乘积项
        prod_sk1 = 1
        prod_ct_sk1 = 1
        for node in nodes_sk1:
            attr = node.getAttributeAndIndex()
            attr_stripped = self.util.strip_index(attr)
            prod_sk1 *= sk1['sk1'][attr_stripped]
            prod_ct_sk1 *= ctxt['ct'][attr]

        # 计算 d0 部分
        e0_sk0 = pair(sk0['sk2'], ctxt['g_s0'])
        e1_sk0 = pair(prod_sk0, ctxt['h_s1'])
        e2_sk0 = pair(prod_ct_sk0, sk0['h_r'])
        d0 = e0_sk0 * (e1_sk0 / e2_sk0)

        # 计算 d1 部分
        e0_sk1 = pair(sk1['sk2'], ctxt['g_s0'])
        e1_sk1 = pair(prod_sk1, ctxt['h_s1'])
        e2_sk1 = pair(prod_ct_sk1, sk1['h_r'])
        d1 = e0_sk1 * (e1_sk1 / e2_sk1)

        # 合并 d0 和 d1 得到最终解密结果
        kem = d0 * d1

        # 解密后的消息是密文Cp除以kem
        plaintext = ctxt['Cp'] / kem

        return plaintext
