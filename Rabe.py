import argparse
import json
import sys

from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
from charm.toolbox.ABEnc import ABEnc
from Msp import MSP
from FABEO import FABECPABE 
import math
import hashlib


class BinaryTree:
    """二叉树结构管理类，用于用户身份和时间管理（基于KUNode逻辑优化最小覆盖集）"""

    def __init__(self, depth):
        self.depth = depth  # 二叉树深度（叶子节点在第depth层）
        self.num_leaves = 2 ** depth  # 叶子节点总数
        self.nodes = self._generate_tree()  # 生成二叉树所有节点
        # 预存：叶子节点索引到"根→叶子路径"的映射（对应KUNode中的user_assignment）
        self.leaf_path_map = self._build_leaf_path_map()

    def _generate_tree(self):
        """生成完整的二叉树节点（层级0为根，层级depth为叶子）"""
        nodes = {}
        for level in range(self.depth + 1):
            for pos in range(2 ** level):
                node_id = self._node_id(level, pos)
                nodes[node_id] = {
                    'level': level,
                    'position': pos,
                    'left_child': self._node_id(level + 1, 2 * pos) if level < self.depth else None,
                    'right_child': self._node_id(level + 1, 2 * pos + 1) if level < self.depth else None,
                    'parent': self._node_id(level - 1, pos // 2) if level > 0 else None
                }
        return nodes

    def _node_id(self, level, position):
        """生成节点ID（格式：level_position，如根节点0_0，第3层第2个节点3_2）"""
        return f"{level}_{position}"

    def _build_leaf_path_map(self):
        """构建"叶子索引→根到叶子路径"的映射（对应KUNode中的user_assignment）"""
        leaf_path_map = {}
        for leaf_index in range(self.num_leaves):
            # 获取当前叶子的根→叶子路径（调用已有的get_path方法）
            path = self.get_path(leaf_index)
            leaf_path_map[leaf_index] = path
        return leaf_path_map

    def get_leaf_node(self, leaf_index):
        """获取叶子节点ID（叶子节点位于最深层depth）"""
        if leaf_index < 0 or leaf_index >= self.num_leaves:
            raise ValueError("Leaf index out of range")
        return self._node_id(self.depth, leaf_index)

    def get_path(self, leaf_index):
        """获取从根到指定叶子的路径（根→叶子顺序）"""
        path = []
        current = self.get_leaf_node(leaf_index)
        while current is not None:
            path.append(current)
            current = self.nodes[current]['parent']
        return list(reversed(path))  # 反转后为"根→叶子"顺序

    def _get_sibling(self, node_id):
        """获取指定节点的兄弟节点ID（根节点无兄弟，返回None）"""
        node = self.nodes[node_id]
        parent = node['parent']
        if parent is None:
            return None
        parent_node = self.nodes[parent]
        return parent_node['right_child'] if node_id == parent_node['left_child'] else parent_node['left_child']

    def get_cover_set(self, revoked_leaves):
        """计算覆盖非撤销用户的最小节点集合（基于KUNode逻辑重构）"""
        # -------------------------- 步骤1：初始化撤销路径集合X --------------------------
        # X：所有被撤销叶子的"根→叶子路径节点"的并集（对应KUNode中的X）
        X = set()
        # 校验被撤销叶子索引合法性，并收集所有撤销路径节点
        for leaf_index in revoked_leaves:
            if leaf_index < 0 or leaf_index >= self.num_leaves:
                raise ValueError(f"Leaf index {leaf_index} out of range (total leaves: {self.num_leaves})")
            # 从预存的leaf_path_map中获取当前叶子的路径，加入X
            X.update(self.leaf_path_map[leaf_index])

        # -------------------------- 步骤2：初始化覆盖集Y --------------------------
        Y = set()
        # 边界条件1：无被撤销叶子→根节点覆盖所有（对应KUNode中RL为空返回root）
        if not revoked_leaves:
            root_id = self._node_id(0, 0)
            Y.add(root_id)
            return sorted(Y)  # 排序后返回，便于阅读

        # -------------------------- 步骤3：处理根节点的直接子节点（第一层节点） --------------------------
        # 根节点ID（0_0）的左子（1_0）和右子（1_1）（对应KUNode中的0b0和0b1）
        root_id = self._node_id(0, 0)
        root_left = self.nodes[root_id]['left_child']  # 1_0
        root_right = self.nodes[root_id]['right_child']  # 1_1
        # 若子节点不在X（无被撤销叶子的路径经过该子节点）→ 加入Y（覆盖其下所有未撤销叶子）
        if root_left not in X:
            Y.add(root_left)
        if root_right not in X:
            Y.add(root_right)

        # -------------------------- 步骤4：遍历撤销路径，处理深层非叶子节点 --------------------------
        # 遍历X中所有非根节点（对应KUNode中遍历theta in X）
        for node_id in X:
            # 跳过根节点（已单独处理）
            if node_id == root_id:
                continue
            # 获取当前节点的层级和子节点（判断是否为非叶子节点）
            node = self.nodes[node_id]
            node_level = node['level']
            left_child = node['left_child']  # 当前节点的左子（node_id+"_0"的对应格式，如2_1的左子是3_2）
            right_child = node['right_child']  # 当前节点的右子

            # 仅处理非叶子节点（子节点存在，即层级<depth）（对应KUNode中len(theta) < tree_depth+2）
            if node_level < self.depth:
                # 左子不在X→未被撤销，加入Y（覆盖左子下的未撤销叶子）
                if left_child not in X:
                    Y.add(left_child)
                # 右子不在X→未被撤销，加入Y（覆盖右子下的未撤销叶子）
                if right_child not in X:
                    Y.add(right_child)

        # -------------------------- 步骤5：返回排序后的覆盖集 --------------------------
        # 排序后返回（按节点层级升序，同层级按位置升序），便于结果验证
        return sorted(Y, key=lambda x: (int(x.split('_')[0]), int(x.split('_')[1])))


class TimePolicyManager:
    """时间策略管理类，处理时间属性转换"""

    def __init__(self, time_depth):
        self.time_depth = time_depth
        self.time_tree = BinaryTree(time_depth)

        # 定义时间属性集合 Ω\' = {ω_{i,b} : i ∈ [log(T)], b ∈ {0,1}}
        self.time_attributes = {}
        for i in range(time_depth):
            self.time_attributes[f"W{i + 1}0"] = (i, 0)
            self.time_attributes[f"W{i + 1}1"] = (i, 1)

    def _get_node_string_representation(self, node_id):
        """
        获取节点的字符串表示（论文中的 b(y)）
        格式：由0,1,*组成的长度为time_depth的字符串
        """
        level, pos = map(int, node_id.split('_'))

        # 构建路径字符串
        path_bits = []
        current_pos = pos
        # 收集从根到当前节点的路径位
        for l in range(1, level + 1):
            bit = current_pos % 2
            path_bits.append(str(bit))
            current_pos = current_pos // 2
        # 反转位的顺序，使高位层级在左侧
        path_bits = path_bits[::-1]

        # 用*填充到time_depth长度（在右侧填充）
        while len(path_bits) < self.time_depth:
            path_bits.append('*')

        return ''.join(path_bits)

    def get_node_attributes(self, node_id):
        node_str = self._get_node_string_representation(node_id)
        attributes = set()
        for i, char in enumerate(node_str):
            if char == '0':
                attributes.add(f"W{i + 1}0")
            elif char == '1':
                attributes.add(f"W{i + 1}1")
            elif char == '*':
                attributes.add(f"W{i + 1}0")
                attributes.add(f"W{i + 1}1")
        return attributes

    def create_time_policy_for_node(self, node_id):
        """
        为节点创建时间策略 (B_y, β_y)
        返回策略字符串表示
        """
        node_str = self._get_node_string_representation(node_id)
        policy_parts = []

        for i, char in enumerate(node_str):
            if char == '0':
                policy_parts.append(f"W{i + 1}0")
            elif char == '1':
                policy_parts.append(f"W{i + 1}1")
            elif char == '*':
                policy_parts.append(f"(W{i + 1}_0 OR W{i + 1}1)")

        return " AND ".join(policy_parts)

    def get_time_policy_for_leaf(self, time_index):
        """
        获取叶子节点对应的时间策略 P_t
        P_t(S) = 1 当且仅当 ∀ i ∈ [log(T)], ω_{i,t[i]} ∈ S
        """
        if time_index < 0 or time_index >= 2 ** self.time_depth:
            raise ValueError("Time index out of range")

        # 将时间索引转换为二进制字符串，填充到time_depth长度
        bin_str = bin(time_index)[2:].zfill(self.time_depth)
        policy_parts = []

        for i, bit in enumerate(bin_str):
            policy_parts.append(f"W{i + 1}{bit}")

        return " AND ".join(policy_parts)

    def is_ancestor(self, ancestor_node, descendant_node):
        """
        判断一个节点是否是另一个节点的祖先
        基于论文中的关键性质：P_t(s_y) = 1 当且仅当 y 是 t 对应叶子的祖先
        """
        ancestor_str = self._get_node_string_representation(ancestor_node)
        descendant_str = self._get_node_string_representation(descendant_node)

        # 检查ancestor_str是否是descendant_str的前缀（*表示通配）
        for a_char, d_char in zip(ancestor_str, descendant_str):
            if a_char != '*' and a_char != d_char:
                return False
        return True

    def get_cover_set_for_time(self, time_index):
        """
        获取时间t对应的覆盖节点集合 T_t（论文Theorem 6.1）
        这里简化实现，返回包含时间t对应叶子祖先的节点集合
        """
        leaf_node = self.time_tree.get_leaf_node(time_index)
        path = self.time_tree.get_path(time_index)
        return path


class RevocableABE:
    """可撤销属性基加密方案（按照文档正确实现）"""

    def __init__(self, group_obj, max_users=65536, max_time_periods=1024, verbose=False):
        """
        初始化可撤销ABE方案

        参数:
        - group_obj: 配对群对象
        - max_users: 最大用户数
        - max_time_periods: 最大时间周期数
        - verbose: 是否输出调试信息
        """
        self.group = group_obj
        self.util = MSP(self.group, verbose)
        self.verbose = verbose

        # 初始化用户树和时间树
        self.user_depth = math.ceil(math.log2(max_users))
        self.time_depth = math.ceil(math.log2(max_time_periods))

        self.user_tree = BinaryTree(self.user_depth)
        self.time_tree = BinaryTree(self.time_depth)
        self.time_policy_manager = TimePolicyManager(self.time_depth)

        # 基础ABE方案
        self.base_abe = FABECPABE(group_obj, verbose)

    def setup(self):
        """初始化算法 - 调用分段式方案的初始化算法生成主公钥和主私钥"""
        if self.verbose:
            print("=== 执行Setup算法 ===")

        # 直接调用基础ABE的setup
        pk, msk = self.base_abe.setup()


        if self.verbose:
            print("系统参数生成完成")

        return pk, msk

    def _user_id_to_leaf_index(self, user_id):
        """将用户ID转换为叶子节点索引"""
        # 使用哈希函数确保均匀分布
        hash_obj = hashlib.sha256(user_id.encode())
        hash_int = int(hash_obj.hexdigest(), 16)
        return hash_int % (2 ** self.user_depth)


    def keygen(self, pk, msk, attr_list, user_id):
        """
        密钥生成算法 - 为用户生成属性密钥（b=0）

        参数:
        - pk: 公钥
        - msk: 主密钥
        - attr_list: 属性列表
        - user_id: 用户标识
        """
        if self.verbose:
            print(f"=== 执行KeyGen算法 (用户: {user_id}) ===")

        # 将用户ID映射到叶子节点
        leaf_index = self._user_id_to_leaf_index(user_id)
        user_path = self.user_tree.get_path(leaf_index)


        # 为路径上的每个节点调用分段式方案（b=0）
        sk_components = {}
        for node_id in user_path:
            # 调用基础ABE生成密钥（b=0）(self, pk, msk, attr_list, U, b)
            sk_component = self.base_abe.keygen(pk, msk, attr_list, node_id, 0)
            sk_components[node_id] = sk_component

        sk = [user_id,sk_components]

        return sk

    def encrypt(self, pk, msg, policy_str, time_period):
        """
        加密算法 - 使用访问策略和时间周期加密消息

        参数:
        - pk: 公钥
        - msg: 消息
        - policy_str: 访问策略字符串
        - time_period: 时间周期
        """
        if self.verbose:
            print(f"=== 执行Encrypt算法 (时间周期: {time_period}) ===")

        # 将时间转换为时间策略
        time_policy_str = self.time_policy_manager.create_time_policy_for_node(time_period)

        if self.verbose:
            print(f"时间策略: {time_policy_str}")
            print(f"属性策略: {policy_str}")

        # 上下拼接策略：属性策略 OR 时间策略
        full_policy_str = f"({policy_str}) OR ({time_policy_str})"

        if self.verbose:
            print(f"完整访问策略: {full_policy_str}")

        # 调用基础ABE加密
        ciphertext = self.base_abe.encrypt(pk, msg, full_policy_str)

        return ciphertext

    def KeyUpdate(self, pk, msk, revocation_list, time_period):
        """
        生成时间time_period对应的密钥更新信息，输出为字典（键为用户节点x，值为基础ABE生成的b=1密钥片段）。

        参数：
            msk: 主密钥
            revocation_list: 撤销的用户ID列表
            time_period: 时间周期（整数）
        返回：
            K_t: 字典，键为覆盖集U(rl)中的用户节点x，值为对应的密钥片段（b=1）
        """
        # ---------- 步骤1：处理用户撤销列表，生成覆盖非撤销用户的节点集合U(rl) ----------
        # 1. 用户ID → 叶子索引
        leaf_indices = [self._user_id_to_leaf_index(user_id) for user_id in revocation_list]
        U_rl = self.user_tree.get_cover_set(leaf_indices)

        # ---------- 步骤2：生成时间周期对应的策略属性集合s_t ----------
        # 获取时间周期对应的时间节点集合（调用TimePolicyManager的方法）
        s_t = self.time_policy_manager.get_node_attributes(time_period)
        # 收集所有时间节点的属性（调用TimePolicyManager的get_node_attributes）


        # ---------- 步骤3：为每个用户节点x生成b=1的密钥片段 ----------
        K_t = {}
        for x in U_rl:
            # 调用基础ABE的keygen（参数：msk, b=1, 属性列表s_t, 用户节点x）
            sk_prime = self.base_abe.keygen(pk, msk, s_t, x, 1)
            K_t[x] = sk_prime

        return K_t

    def decrypt(self, pk, ciphertext, user_sk, key_update_info, revocation_list):
        """
        解密算法 - 验证用户撤销状态并完成解密（调用基础ABE的双密钥解密接口）

        参数:
        - pk: 公钥
        - ciphertext: 密文
        - user_sk: 用户私钥
        - key_update_info: 密钥更新信息（来自KeyUpdate）
        - revocation_list: 撤销列表
        """
        if self.verbose:
            print("=== 执行Decrypt算法 ===")

        # -------------------------- 步骤1：提取用户私钥核心信息 --------------------------
        # 解析user_sk结构（keygen输出为 [user_id, sk0_components]）
        user_id = user_sk[0]
        sk0_components = user_sk[1]  # b=0的密钥片段集合，键为用户路径节点ID

        # -------------------------- 步骤2：检查用户是否被撤销 --------------------------
        if user_id in revocation_list:
            error_msg = f"用户 {user_id} 已被撤销，无法解密"
            if self.verbose:
                print(error_msg)
            raise Exception(error_msg)

        # -------------------------- 步骤3：找到共同的节点ID --------------------------
        # 找到sk0_components和key_update_info中共同的键
        common_nodes = set(sk0_components.keys()) & set(key_update_info.keys())

        # 根据逻辑，应该有且仅有一个共同节点
        if len(common_nodes) != 1:
            error_msg = f"错误：找到 {len(common_nodes)} 个共同节点，预期为1个"
            if self.verbose:
                print(error_msg)
            raise Exception(error_msg)

        common_node = common_nodes.pop()
        if self.verbose:
            print(f"找到共同节点：{common_node}")

        # -------------------------- 步骤4：获取对应的密钥片段并解密 --------------------------
        sk0 = sk0_components[common_node]
        sk1 = key_update_info[common_node]

        # 调用基础ABE的解密方法
        plaintext = self.base_abe.decrypt(pk, ciphertext, sk0, sk1)

        # ========== 新增：检查解密结果 ==========
        if plaintext is None:
            raise Exception("解密失败：属性不满足访问策略")

        if self.verbose:
            print("解密成功")

        return str(plaintext)


# 在Python脚本的main函数中添加详细的错误处理
def main():
    parser = argparse.ArgumentParser(description='Revocable ABE Test')
    parser.add_argument('--message', type=str, required=True, help='Message to encrypt')
    parser.add_argument('--policy', type=str, required=True, help='Access policy')
    parser.add_argument('--attributes', type=str, required=True, help='Comma-separated list of attributes')
    parser.add_argument('--user_id', type=str, required=True, help='User ID')
    parser.add_argument('--time_period', type=str, required=True, help='Time period')
    parser.add_argument('--revoked_users', type=str, default='', help='Comma-separated list of revoked user IDs')

    args = parser.parse_args()

    try:
        # 初始化环境
        group = PairingGroup('MNT224')
        abe = RevocableABE(
            group,
            max_users=16,
            max_time_periods=8,
            verbose=False
        )

        # 系统初始化
        pk, msk = abe.setup()

        # 为用户生成密钥
        attrs = args.attributes.split(',')
        user_sk = abe.keygen(pk, msk, attrs, args.user_id)

        # 加密消息
        message = group.init(GT, int(args.message))
        ciphertext = abe.encrypt(pk, message, args.policy, args.time_period)

        # 生成密钥更新信息
        revoked_list = args.revoked_users.split(',') if args.revoked_users else []
        key_update = abe.KeyUpdate(pk, msk, revoked_list, args.time_period)

        # 尝试解密
        try:
            decrypted_msg = abe.decrypt(pk, ciphertext, user_sk, key_update, revoked_list)
            plaintext = str(decrypted_msg)
            success = True
        except Exception as e:
            plaintext = str(e)
            success = False

        # 准备输出结果
        result = {
            'pk': str(pk),
            'msk': str(msk),
            'ct': str(ciphertext),
            'sk': str(user_sk),
            'plaintext': plaintext,
            'success': success
        }

        # 输出JSON格式的结果
        print(json.dumps(result))
        sys.stdout.flush()

    except Exception as e:
        # 如果发生异常，输出错误信息
        import traceback
        error_result = {
            'error': str(e),
            'traceback': traceback.format_exc()
        }
        print(json.dumps(error_result))
        sys.stdout.flush()
        sys.exit(1)


#if __name__ == "__main__":
#    main()

def test_three_users():
    """测试三个用户：一个正常满足策略且不撤销，另一个满足策略但被撤销，第三个不满足策略但不撤销"""
    # 1. 初始化环境
    group = PairingGroup('MNT224')
    abe = RevocableABE(
        group,
        max_users=16,
        max_time_periods=8,
        verbose=True
    )

    # 2. 系统初始化
    pk, msk = abe.setup()
    print("\\n【系统参数】")
    print(f"PK: {pk}")
    print(f"MSK: {msk}")

    # 3. 生成三个用户密钥
    user1_id = "user1"
    user2_id = "user2"
    user3_id = "user3"
    user1_attrs = ["DOCTOR", "CARDIOLOGY"]
    user2_attrs = ["DOCTOR", "CARDIOLOGY"]
    user3_attrs = ["NURSE", "ORTHOPEDICS"]

    print("\\n=== 为用户1生成密钥 ===")
    user1_sk = abe.keygen(pk, msk, user1_attrs, user1_id)
    print(f"用户1叶子索引: {abe._user_id_to_leaf_index(user1_id)}")
    print(f"用户1路径: {abe.user_tree.get_path(abe._user_id_to_leaf_index(user1_id))}")

    print("\\n=== 为用户2生成密钥 ===")
    user2_sk = abe.keygen(pk, msk, user2_attrs, user2_id)
    print(f"用户2叶子索引: {abe._user_id_to_leaf_index(user2_id)}")
    print(f"用户2路径: {abe.user_tree.get_path(abe._user_id_to_leaf_index(user2_id))}")

    print("\\n=== 为用户3生成密钥 ===")
    user3_sk = abe.keygen(pk, msk, user3_attrs, user3_id)
    print(f"用户3叶子索引: {abe._user_id_to_leaf_index(user3_id)}")
    print(f"用户3路径: {abe.user_tree.get_path(abe._user_id_to_leaf_index(user3_id))}")

    # 4. 加密消息
    message = group.random(GT)
    
    print("\\n【加密阶段】")
    print(f"原始消息 (GT元素): {message}")
    print(f"原始消息类型: {type(message)}")

    access_policy = "DOCTOR and CARDIOLOGY"
    target_time = "3_1"

    print(f"\\n访问策略: {access_policy}")
    print(f"时间周期: {target_time}")

    print("\\n=== 开始加密 ===")
    ciphertext = abe.encrypt(pk, message, access_policy, target_time)
    
    print("\\n【密文组件】")
    print(f"策略 (policy): {ciphertext['policy']}")
    print(f"g_s0: {ciphertext['g_s0']}")
    print(f"h_s1: {ciphertext['h_s1']}")
    print(f"ct (属性密文): {ciphertext['ct']}")
    print(f"Cp (最终密文): {ciphertext['Cp']}")

    # 5. 生成密钥更新信息（撤销user2）
    revoked_users = [user2_id]
    
    print("\\n【撤销列表】")
    print(f"被撤销用户: {revoked_users}")
    
    # 计算覆盖集
    revoked_leaf_indices = [abe._user_id_to_leaf_index(uid) for uid in revoked_users]
    cover_set = abe.user_tree.get_cover_set(revoked_leaf_indices)
    print(f"撤销叶子索引: {revoked_leaf_indices}")
    print(f"覆盖集U(rl): {cover_set}")

    print("\\n=== 生成密钥更新信息 ===")
    key_update = abe.KeyUpdate(pk, msk, revoked_users, target_time)
    
    print("\\n【密钥更新信息】")
    for node_id, sk in key_update.items():
        print(f"节点 {node_id}:")
        print(f"  属性列表: {sk['attr_list']}")
        print(f"  sk1 (时间属性密钥): {sk['sk1']}")
        print(f"  sk2: {sk['sk2']}")

    # 6. 测试用户1（未撤销，满足策略）的解密
    print("\\n" + "="*60)
    print("【测试用户1】未撤销，满足策略 (DOCTOR & CARDIOLOGY)")
    print("="*60)
    
    try:
        # 找到共同节点
        user1_sk0 = user1_sk[1]
        common_nodes_1 = set(user1_sk0.keys()) & set(key_update.keys())
        print(f"用户1路径节点: {list(user1_sk0.keys())}")
        print(f"密钥更新节点: {list(key_update.keys())}")
        print(f"共同节点: {common_nodes_1}")
        
        decrypted_msg1 = abe.decrypt(pk, ciphertext, user1_sk, key_update, revoked_users)
        
        print(f"\\n【解密结果】")
        print(f"原始消息: {message}")
        print(f"解密消息: {decrypted_msg1}")
        print(f"原始消息类型: {type(message)}")
        print(f"解密消息类型: {type(decrypted_msg1)}")
        
        # 输出中间计算值（在FABEO.decrypt中添加）
        print(f"\\n【详细对比】")
        print(f"原始消息str: {str(message)}")
        print(f"解密消息str: {str(decrypted_msg1)}")
        print(f"字符串相等: {str(decrypted_msg1) == str(message)}")
        
        # 尝试序列化比较
        try:
            orig_serial = abe.group.serialize(message)
            dec_serial = abe.group.serialize(decrypted_msg1)
            print(f"\\n原始序列化: {orig_serial[:50]}...")
            print(f"解密序列化: {dec_serial[:50]}...")
            print(f"序列化相等: {orig_serial == dec_serial}")
        except Exception as e:
            print(f"序列化失败: {e}")
        
    except Exception as e:
        print(f"\\n用户1解密异常: {e}")
        import traceback
        traceback.print_exc()

    # 7. 测试用户2（已撤销，满足策略）的解密 - 应该失败
    print("\\n" + "="*60)
    print("【测试用户2】已撤销，满足策略 (DOCTOR & CARDIOLOGY)")
    print("="*60)
    
    try:
        user2_sk0 = user2_sk[1]
        common_nodes_2 = set(user2_sk0.keys()) & set(key_update.keys())
        print(f"用户2路径节点: {list(user2_sk0.keys())}")
        print(f"密钥更新节点: {list(key_update.keys())}")
        print(f"共同节点: {common_nodes_2}")
        
        decrypted_msg2 = abe.decrypt(pk, ciphertext, user2_sk, key_update, revoked_users)
        
        print(f"\\n【解密结果】")
        print(f"解密消息: {decrypted_msg2}")
        print("⚠ 警告: 用户2已被撤销但解密成功！")
        
    except Exception as e:
        print(f"\\n✓ 预期行为: 用户2解密失败")
        print(f"错误信息: {e}")

    # 8. 测试用户3（未撤销，不满足策略）的解密 - 应该失败
    print("\\n" + "="*60)
    print("【测试用户3】未撤销，不满足策略 (NURSE & ORTHOPEDICS)")
    print("="*60)
    
    try:
        user3_sk0 = user3_sk[1]
        common_nodes_3 = set(user3_sk0.keys()) & set(key_update.keys())
        print(f"用户3路径节点: {list(user3_sk0.keys())}")
        print(f"密钥更新节点: {list(key_update.keys())}")
        print(f"共同节点: {common_nodes_3}")
        
        decrypted_msg3 = abe.decrypt(pk, ciphertext, user3_sk, key_update, revoked_users)
        
        print(f"\\n【解密结果】")
        print(f"解密消息: {decrypted_msg3}")
        print("⚠ 警告: 用户3不满足策略但解密成功！")
        
    except Exception as e:
        print(f"\\n✓ 预期行为: 用户3解密失败")
        print(f"错误信息: {e}")

    print("\\n" + "="*60)
    print("【测试完成】")
    print("="*60)


if __name__ == "__main__":
    test_three_users()

