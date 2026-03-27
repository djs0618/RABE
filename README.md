# RFABE: Revocable Fast Attribute-Based Encryption

基于分段式密钥生成的可撤销属性基加密方案，支持即时用户撤销。

## 依赖

- Python 3.8+
- Charm-Crypto 0.5（需先安装GMP、PBC库）
- pyparsing

## 文件说明
-FABEO.py ：基础分段式CP-ABE，包括Setup/KeyGen/Encrypt/Decrypt
-Rabe.py ：可撤销ABE，包括用户撤销树、时间策略、密钥更新
-Msp.py ：LSSS访问结构
-policytree.py ：策略解析
-secretutil.py ：密钥工具

## 测试
python3 Rabe.py
