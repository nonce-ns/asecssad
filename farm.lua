local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 152) then
					if (Enum <= 75) then
						if (Enum <= 37) then
							if (Enum <= 18) then
								if (Enum <= 8) then
									if (Enum <= 3) then
										if (Enum <= 1) then
											if (Enum == 0) then
												Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
											else
												local K;
												local B;
												local A;
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												B = Inst[3];
												K = Stk[B];
												for Idx = B + 1, Inst[4] do
													K = K .. Stk[Idx];
												end
												Stk[Inst[2]] = K;
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]]();
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Upvalues[Inst[3]] = Stk[Inst[2]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												if Stk[Inst[2]] then
													VIP = VIP + 1;
												else
													VIP = Inst[3];
												end
											end
										elseif (Enum > 2) then
											local B;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Inst[2] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum <= 5) then
										if (Enum == 4) then
											local B;
											local A;
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
										elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = VIP + Inst[3];
										end
									elseif (Enum <= 6) then
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									elseif (Enum == 7) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									else
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 13) then
									if (Enum <= 10) then
										if (Enum == 9) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										end
									elseif (Enum <= 11) then
										Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
									elseif (Enum == 12) then
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									else
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 15) then
									if (Enum == 14) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum <= 16) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								elseif (Enum > 17) then
									Stk[Inst[2]] = {};
								else
									Upvalues[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 27) then
								if (Enum <= 22) then
									if (Enum <= 20) then
										if (Enum > 19) then
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										else
											local A;
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										end
									elseif (Enum == 21) then
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
									end
								elseif (Enum <= 24) then
									if (Enum == 23) then
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 25) then
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 26) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 32) then
								if (Enum <= 29) then
									if (Enum > 28) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 30) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 31) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 34) then
								if (Enum > 33) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 35) then
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 36) then
								local B;
								local T;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							elseif (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 56) then
							if (Enum <= 46) then
								if (Enum <= 41) then
									if (Enum <= 39) then
										if (Enum > 38) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Stk[Inst[2]] < Inst[4]) then
												VIP = Inst[3];
											else
												VIP = VIP + 1;
											end
										else
											local B;
											local A;
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
										end
									elseif (Enum > 40) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								elseif (Enum <= 43) then
									if (Enum == 42) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Inst[2] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 44) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 45) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 51) then
								if (Enum <= 48) then
									if (Enum == 47) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 49) then
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 50) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 53) then
								if (Enum > 52) then
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 54) then
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 55) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 65) then
							if (Enum <= 60) then
								if (Enum <= 58) then
									if (Enum > 57) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum > 59) then
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 62) then
								if (Enum > 61) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 63) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum == 64) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 70) then
							if (Enum <= 67) then
								if (Enum == 66) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum <= 68) then
								local T;
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							elseif (Enum > 69) then
								VIP = Inst[3];
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 72) then
							if (Enum == 71) then
								do
									return Stk[Inst[2]];
								end
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 73) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Enum > 74) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 113) then
						if (Enum <= 94) then
							if (Enum <= 84) then
								if (Enum <= 79) then
									if (Enum <= 77) then
										if (Enum == 76) then
											local B;
											local T;
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											T = Stk[A];
											B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										else
											local K;
											local B;
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum > 78) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 81) then
									if (Enum == 80) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum <= 82) then
									Stk[Inst[2]] = Stk[Inst[3]];
								elseif (Enum == 83) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] > Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = VIP + Inst[3];
									end
								end
							elseif (Enum <= 89) then
								if (Enum <= 86) then
									if (Enum > 85) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									end
								elseif (Enum <= 87) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 88) then
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 91) then
								if (Enum > 90) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 92) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum > 93) then
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 103) then
							if (Enum <= 98) then
								if (Enum <= 96) then
									if (Enum == 95) then
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum == 97) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 100) then
								if (Enum == 99) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 101) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 102) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 108) then
							if (Enum <= 105) then
								if (Enum > 104) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								end
							elseif (Enum <= 106) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 107) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 110) then
							if (Enum == 109) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 111) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 112) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						else
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 132) then
						if (Enum <= 122) then
							if (Enum <= 117) then
								if (Enum <= 115) then
									if (Enum == 114) then
										local A;
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum > 116) then
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								else
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum <= 119) then
								if (Enum > 118) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 120) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum > 121) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 127) then
							if (Enum <= 124) then
								if (Enum == 123) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 125) then
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum > 126) then
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 129) then
							if (Enum > 128) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 130) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum > 131) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
						end
					elseif (Enum <= 142) then
						if (Enum <= 137) then
							if (Enum <= 134) then
								if (Enum == 133) then
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 135) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 136) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] > Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = VIP + Inst[3];
								end
							end
						elseif (Enum <= 139) then
							if (Enum > 138) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 140) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 141) then
							Stk[Inst[2]] = Inst[3];
						else
							local A = Inst[2];
							local Cls = {};
							for Idx = 1, #Lupvals do
								local List = Lupvals[Idx];
								for Idz = 0, #List do
									local Upv = List[Idz];
									local NStk = Upv[1];
									local DIP = Upv[2];
									if ((NStk == Stk) and (DIP >= A)) then
										Cls[DIP] = NStk[DIP];
										Upv[1] = Cls;
									end
								end
							end
						end
					elseif (Enum <= 147) then
						if (Enum <= 144) then
							if (Enum == 143) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum <= 145) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						elseif (Enum > 146) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 149) then
						if (Enum == 148) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local T;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 150) then
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = #Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					elseif (Enum == 151) then
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 228) then
					if (Enum <= 190) then
						if (Enum <= 171) then
							if (Enum <= 161) then
								if (Enum <= 156) then
									if (Enum <= 154) then
										if (Enum > 153) then
											local A;
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Stk[Inst[2]] < Inst[4]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A;
											local K;
											local B;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum > 155) then
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 158) then
									if (Enum == 157) then
										local Edx;
										local Results;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A;
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 159) then
									local Results;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum > 160) then
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 166) then
								if (Enum <= 163) then
									if (Enum > 162) then
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 164) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 165) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 168) then
								if (Enum > 167) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 169) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							elseif (Enum == 170) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 180) then
							if (Enum <= 175) then
								if (Enum <= 173) then
									if (Enum > 172) then
										if (Stk[Inst[2]] <= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 174) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum <= 177) then
								if (Enum == 176) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 178) then
								do
									return;
								end
							elseif (Enum == 179) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 185) then
							if (Enum <= 182) then
								if (Enum == 181) then
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 183) then
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 184) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 187) then
							if (Enum == 186) then
								Stk[Inst[2]]();
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 188) then
							local B;
							local T;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						elseif (Enum > 189) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 209) then
						if (Enum <= 199) then
							if (Enum <= 194) then
								if (Enum <= 192) then
									if (Enum > 191) then
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									else
										Stk[Inst[2]] = -Stk[Inst[3]];
									end
								elseif (Enum > 193) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 196) then
								if (Enum > 195) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 197) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 198) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 204) then
							if (Enum <= 201) then
								if (Enum == 200) then
									local Edx;
									local Results;
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 202) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 203) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 206) then
							if (Enum > 205) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 207) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
						elseif (Enum > 208) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = -Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 218) then
						if (Enum <= 213) then
							if (Enum <= 211) then
								if (Enum == 210) then
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] < Inst[4]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum == 212) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 215) then
							if (Enum > 214) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 216) then
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						elseif (Enum > 217) then
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 223) then
						if (Enum <= 220) then
							if (Enum > 219) then
								local B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 221) then
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Enum == 222) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local A;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 225) then
						if (Enum > 224) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 226) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 227) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					end
				elseif (Enum <= 266) then
					if (Enum <= 247) then
						if (Enum <= 237) then
							if (Enum <= 232) then
								if (Enum <= 230) then
									if (Enum == 229) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum > 231) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum <= 234) then
								if (Enum > 233) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = -Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 235) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 236) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
							end
						elseif (Enum <= 242) then
							if (Enum <= 239) then
								if (Enum > 238) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 240) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 241) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 244) then
							if (Enum > 243) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 245) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 246) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 256) then
						if (Enum <= 251) then
							if (Enum <= 249) then
								if (Enum == 248) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								end
							elseif (Enum == 250) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 253) then
							if (Enum == 252) then
								local Edx;
								local Results;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 254) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 255) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A = Inst[2];
							local Results = {Stk[A](Stk[A + 1])};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 261) then
						if (Enum <= 258) then
							if (Enum == 257) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local Edx;
								local Results;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 259) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 260) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Inst[4]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum <= 263) then
						if (Enum == 262) then
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 264) then
						local A;
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					elseif (Enum == 265) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] < Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 285) then
					if (Enum <= 275) then
						if (Enum <= 270) then
							if (Enum <= 268) then
								if (Enum > 267) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 269) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum <= 272) then
							if (Enum > 271) then
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 82) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 273) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 274) then
							local B;
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 280) then
						if (Enum <= 277) then
							if (Enum > 276) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							end
						elseif (Enum <= 278) then
							local T;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						elseif (Enum > 279) then
							local A;
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 282) then
						if (Enum == 281) then
							local A;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 283) then
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 284) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					else
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum <= 295) then
					if (Enum <= 290) then
						if (Enum <= 287) then
							if (Enum > 286) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 288) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						elseif (Enum == 289) then
							if (Stk[Inst[2]] <= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 292) then
						if (Enum == 291) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 293) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 294) then
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					else
						local K;
						local B;
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 300) then
					if (Enum <= 297) then
						if (Enum > 296) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 298) then
						local B;
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					elseif (Enum == 299) then
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local K;
						local B;
						local A;
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = #Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 302) then
					if (Enum > 301) then
						local A;
						A = Inst[2];
						Stk[A] = Stk[A]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 303) then
					if (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = Inst[3];
					else
						VIP = VIP + 1;
					end
				elseif (Enum > 304) then
					local A;
					Stk[Inst[2]] = {};
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Inst[4];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Inst[4];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Inst[4];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Stk[A + 1]);
				else
					local A = Inst[2];
					do
						return Unpack(Stk, A, A + Inst[3]);
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!DB3Q0003043Q007469636B026Q003E4003043Q007461736B03043Q0077616974026Q00E03F03023Q005F4703053Q00466F72676503043Q005461627303043Q004661726D03043Q007761726E034B3Q005B466F726765204661726D5D20466F726765205549206E6F742072656164792061667465722074696D656F75743B206661726D206D6F64756C65206E6F7420696E697469616C697A65642E03043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030A3Q0052756E5365727669636503113Q005265706C69636174656453746F7261676503093Q00576F726B737061636503083Q004175746F4661726D0100030C3Q0053656C65637465644D6F6273030D3Q004D6F625072696F726974696573030F3Q005072696F72697479456E61626C65642Q0103093Q00426C61636B6C69737403123Q0049676E6F7265496E76756C6E657261626C6503093Q0044656275674D6F646503083Q0044697374616E6365026Q002440030B3Q00412Q7461636B44656C6179029A5Q99B93F03063Q0048656967687403083Q00466C7953702Q6564026Q003640030A3Q00466C696768744D6F646503053Q0041626F7665030A3Q0047686F737453702Q6564030B3Q0047686F73744F2Q66736574026Q000CC003093Q004661726D52616E6765025Q00409F4003133Q00446972656374436861736544697374616E6365026Q007940030B3Q005A6F6E65456E61626C6564030A3Q005A6F6E6543656E74657203013Q0058028Q0003013Q005903013Q005A03083Q005A6F6E654C656674026Q00394003093Q005A6F6E65526967687403093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B03063Q005A6F6E655570026Q002E4003083Q005A6F6E65446F776E026Q001440030A3Q0043616D6572614D6F6465030A3Q004C6F636B546172676574030C3Q0043616D657261486569676874026Q00F03F030E3Q0043616D65726144697374616E6365026Q003240030A3Q0043616D6572615369646503123Q004D61696E74656E616E6365456E61626C656403133Q004D61696E74656E616E6365496E74657276616C026Q004E40031A3Q004D61696E74656E616E6365412Q7461636B5468726573686F6C6403093Q0053702Q65644E656172029A5Q99E93F030B3Q0053702Q6564536C6F776D6F02CD5QCCFC3F030D3Q0053702Q6564412Q70726F61636803083Q0053702Q6564466172026Q00F83F03113Q005361666548656967687444656661756C74025Q00806640030F3Q0053616665486569676874537061776E030E3Q005361666548656967687449646C6503103Q00537061776E436865636B52616469757303103Q00526F746174696F6E446561645A6F6E65026Q000C4003163Q00526F746174696F6E446561645A6F6E6554726176656C03103Q00486F72697A6F6E74616C4F2Q66736574030E3Q00537475636B446574656374696F6E03073Q00456E61626C6564030B3Q005468726573686F6C644C31030B3Q005468726573686F6C644C32030B3Q005468726573686F6C644C33026Q004940030D3Q0054696D655468726573686F6C64030E3Q00476C6974636844697374616E6365026Q00184003103Q005265636F76657279432Q6F6C646F776E026Q00084003113Q00506F736974696F6E5468726573686F6C64030C3Q00506F736974696F6E54696D6503053Q00706169727303043Q007479706503053Q007461626C65030D3Q0043752Q72656E7454617267657400030C3Q0043752Q72656E745068617365030A3Q00536B69704672616D657303103Q00536B6970412Q7461636B4672616D6573030F3Q0042656C6F7744657363656E64696E6703123Q004F726967696E616C43616D6572615479706503113Q004F726967696E616C43616D65726152656603103Q0043616D657261436F2Q6E656374696F6E03103Q0053652Q73696F6E537461727454696D65030A3Q00546F74616C4B692Q6C7303133Q004C6173744D61696E74656E616E636554696D6503103Q004D61696E74656E616E6365436F756E74031A3Q004C6173744D61696E74656E616E6365412Q7461636B436F756E74030C3Q004C617374506F736974696F6E030C3Q00537475636B436F756E746572030E3Q004C6173744C2Q6F6B546172676574030E3Q004C61737454726176656C4C2Q6F6B030C3Q004C617374542Q6F6C5761726E030F3Q004C6173745265667265736854696D65030C3Q004C6173745461726765744850030D3Q004C617374546172676574526566030D3Q004C617374546172676574506F7303113Q004C617374546172676574506F7354696D6503143Q00412Q7461636B7353696E636548504368616E6765030E3Q00537475636B436865636B54696D65030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D65030E3Q004C32412Q74656D7074436F756E7403113Q004C6173745072696F72697479436865636B030A3Q004661726D436F6E66696703113Q004661726D44656661756C74436F6E666967030E3Q004661726D5549456C656D656E747303073Q00436C65616E757003063Q00696E73657274030D3Q00556E6C6F6164436C65616E7570032C3Q0020466F726765206D692Q73696E673B20636C65616E757020682Q6F6B73206E6F742072656769737465726564030D3Q0043726561746553656374696F6E03093Q004175746F204661726D030E3Q004175746F4661726D546F2Q676C65030C3Q00437265617465546F2Q676C6503043Q004E616D6503103Q00456E61626C65204175746F204661726D030C3Q0043752Q72656E7456616C756503043Q00466C616703123Q004661726D4175746F4661726D546F2Q676C6503083Q0043612Q6C6261636B03143Q00537475636B446574656374696F6E546F2Q676C6503113Q00416E74692D537475636B2053797374656D03183Q004661726D537475636B446574656374696F6E546F2Q676C65030C3Q0043726561746542752Q746F6E030E3Q0020466F72636520436C65616E7570030E3Q002053652Q73696F6E20537461747303103Q005461726765742053656C656374696F6E030B3Q004D6F6244726F70646F776E030E3Q0043726561746544726F70646F776E030B3Q0053656C656374204D6F627303073Q004F7074696F6E73030D3Q004E6F206D6F627320666F756E64030D3Q0043752Q72656E744F7074696F6E030F3Q004D756C7469706C654F7074696F6E73030F3Q004661726D4D6F6244726F70646F776E03083Q004D6F624C6162656C030B3Q004372656174654C6162656C03013Q002003063Q00636F6E63617403023Q002C20030A3Q0028612Q6C206D6F62732903103Q005461726765742046696C746572696E6703113Q00426C61636B6C69737444726F70646F776E030E3Q00426C61636B6C697374204D6F627303153Q004661726D426C61636B6C69737444726F70646F776E03113Q0049676E6F7265496E76756C546F2Q676C6503183Q0049676E6F726520496E76756C6E657261626C6520466C6167030F3Q004661726D49676E6F7265496E76756C03103Q0052656672657368204D6F62204C697374030F3Q005072696F726974792053797374656D030E3Q005072696F72697479546F2Q676C65030F3Q00456E61626C65205072696F7269747903123Q004661726D5072696F72697479546F2Q676C65030D3Q005072696F726974794C6162656C031C3Q002053656C65637420322B206D6F627320666F72207072696F72697479030E3Q002052657665727365204F7264657203103Q00436C656172205072696F726974696573030D3Q004D6F64652053652Q74696E677303123Q00466C696768744D6F646544726F70646F776E030B3Q00466C69676874204D6F646503053Q0042656C6F77030E3Q004661726D466C696768744D6F646503123Q0043616D6572614D6F646544726F70646F776E030B3Q0043616D657261204D6F646503043Q004E6F6E65030B3Q0046697865644F2Q66736574030E3Q004661726D43616D6572614D6F6465030F3Q0043726561746550617261677261706803053Q005469746C6503123Q0020416476616E6365642053652Q74696E677303073Q00436F6E74656E7403333Q0053702Q65642C204865696768742C2043616D65726120736C69646572732061726520696E2074686520504C4159455220746162030C3Q005A6F6E65204661726D696E67030A3Q005A6F6E65546F2Q676C65030B3Q00456E61626C65205A6F6E65030E3Q004661726D5A6F6E65546F2Q676C6503143Q00536574205A6F6E652043656E7465722048657265030E3Q005A6F6E6553697A65536C69646572030C3Q00437265617465536C6964657203093Q005A6F6E652053697A6503053Q0052616E6765026Q00694003093Q00496E6372656D656E74030C3Q004661726D5A6F6E6553697A6503093Q0052657365744661726D03083Q0053746F704661726D030B3Q004661726D204D6F64756C65030C3Q0076342E30204C6F616465642103083Q004475726174696F6E027Q004003053Q007072696E7403243Q005B54686520466F7267655D204661726D206D6F64756C652076342E30206C6F616465642100AE022Q0012FD3Q00014Q00BE3Q0001000200128D000100024Q001600025Q0012FD000300033Q0020A900030003000400122Q000400056Q00030002000100122Q000300063Q00202Q00030003000700062Q00020015000100030004463Q001500010012FD000300063Q0020140003000300070020140003000300080006DC00020015000100030004463Q001500010012FD000300063Q0020140003000300070020140003000300080020140002000300090006EE0002001C000100010004463Q001C00010012FD000300014Q00BE0003000100022Q0014010300033Q0006AD00010004000100030004463Q000400010006EE00020022000100010004463Q002200010012FD0003000A3Q00128D0004000B4Q00730003000200012Q00B23Q00013Q0012FD0003000C3Q00205000030003000D00122Q0005000E6Q00030005000200122Q0004000C3Q00202Q00040004000D00122Q0006000F6Q00040006000200122Q0005000C3Q00202Q00050005000D00122Q000700106Q00050007000200122Q0006000C3Q00202Q00060006000D00122Q000800116Q00060008000200122Q000700063Q00202Q00070007000700202Q00080007000800202Q0008000800094Q00093Q001B00302Q0009001200134Q000A5Q00102Q00090014000A4Q000A5Q00102Q00090015000A00302Q0009001600174Q000A5Q00102Q00090018000A00302Q00090019001300302Q0009001A001300302Q0009001B001C00302Q0009001D001E00302Q0009001F001C00302Q00090020002100302Q00090022002300302Q00090024000200302Q00090025002600302Q00090027002800302Q00090029002A00302Q0009002B00134Q000A3Q000300302Q000A002D002E00302Q000A002F002E00302Q000A0030002E00102Q0009002C000A00302Q00090031003200302Q00090033003200302Q00090034003200302Q00090035003200302Q00090036003700302Q00090038003900302Q0009003A003B00302Q0009003C003D00302Q0009003E003F00302Q00090040002E00302Q00090041001700302Q00090042004300302Q00090044002A00302Q00090045004600302Q00090047004800302Q00090049000500302Q0009004A004B00302Q0009004C004D00302Q0009004E004D00302Q0009004F004D00302Q00090050002800302Q00090051005200302Q00090053000500302Q00090054002E4Q000A3Q000900302Q000A0056001700302Q000A0057003700302Q000A0058000200302Q000A0059005A00302Q000A005B003700302Q000A005C005D00302Q000A005E005F00302Q000A0060005F00302Q000A0061003900102Q00090055000A2Q0020010A5Q00122Q000B00626Q000C00096Q000B0002000D00044Q008900010012FD001000634Q00520011000F4Q000E0110000200020026AC00100088000100640004463Q008800012Q001200106Q0008000A000E001000122Q001000626Q0011000F6Q00100002001200044Q008500012Q003F0015000A000E2Q00C000150013001400067F00100083000100020004463Q008300010004463Q008900012Q00C0000A000E000F00067F000B0078000100020004463Q007800012Q0012000B3Q0017003098000B0065006600302Q000B0067002E00302Q000B0068002E00302Q000B0069002E00302Q000B006A001300302Q000B006B006600302Q000B006C006600302Q000B006D006600302Q000B006E002E00302Q000B006F002E003098000B0070002E00302Q000B0071002E00302Q000B0072002E00302Q000B0073006600302Q000B0074002E00302Q000B0075006600302Q000B0076006600302Q000B0077006600302Q000B0078002E00302Q000B00790066003005010B007A0066003005010B007B0066003023010B007C002E00302Q000B007D002E00302Q000B007E002E00302Q000B007F002E00302Q000B0080002E00302Q000B0081002E00302Q000B0082002E4Q000C5Q00122Q000D00063Q002039000D000D000700102Q000D0083000A00122Q000D00063Q00202Q000D000D000700102Q000D008400090012AE000D00063Q00202Q000D000D000700102Q000D0085000C4Q000D00116Q00128Q00138Q001400153Q00061001163Q000100012Q00523Q000A3Q00061001170001000100012Q00523Q00073Q00020B001800023Q00061001190003000100022Q00523Q00034Q00523Q00063Q00020B001A00043Q00020B001B00053Q000610011C0006000100032Q00523Q00064Q00523Q00034Q00523Q00183Q000610011D0007000100012Q00523Q000A3Q000610011E0008000100042Q00523Q00064Q00523Q000A4Q00523Q00184Q00523Q001D4Q001D011F001F3Q00128D0020002E3Q00061001210009000100032Q00523Q001F4Q00523Q00204Q00523Q00063Q0006100122000A000100072Q00523Q000A4Q00523Q00184Q00523Q00194Q00523Q001A4Q00523Q00214Q00523Q001E4Q00523Q00163Q0006100123000B000100072Q00523Q00194Q00523Q001A4Q00523Q00214Q00523Q001E4Q00523Q000A4Q00523Q00184Q00523Q00163Q00128D0024002E3Q00128D0025002E4Q001D012600263Q0006100127000C000100012Q00523Q000B3Q0006100128000D000100062Q00523Q000B4Q00523Q00194Q00523Q001A4Q00523Q00164Q00523Q000A4Q00523Q00283Q0006100126000E000100052Q00523Q000A4Q00523Q000B4Q00523Q00274Q00523Q001A4Q00523Q00283Q0006100129000F000100082Q00523Q000A4Q00523Q00244Q00523Q00254Q00523Q00164Q00523Q00054Q00523Q000B4Q00523Q00194Q00523Q00263Q000610012A0010000100032Q00523Q000D4Q00523Q00164Q00523Q00063Q000610012B0011000100052Q00523Q000D4Q00523Q002A4Q00523Q00164Q00523Q00064Q00523Q000A3Q000610012C0012000100022Q00523Q000D4Q00523Q00163Q000610012D0013000100012Q00523Q00063Q000610012E0014000100072Q00523Q000A4Q00523Q002D4Q00523Q000B4Q00523Q00164Q00523Q00044Q00523Q00194Q00523Q001A3Q000610012F0015000100032Q00523Q000B4Q00523Q00164Q00523Q002D3Q00128D0030002E4Q001D013100313Q00061001320016000100042Q00523Q00314Q00523Q00304Q00523Q00064Q00523Q000A3Q00061001330017000100012Q00523Q000A3Q00061001340018000100092Q00523Q002B4Q00523Q001B4Q00523Q00164Q00523Q00334Q00523Q00324Q00523Q000A4Q00523Q000B4Q00523Q00294Q00523Q000E3Q00061001350019000100032Q00523Q00194Q00523Q001A4Q00523Q000E3Q0006100136001A000100062Q00523Q00124Q00523Q00354Q00523Q002C4Q00523Q000F4Q00523Q00114Q00523Q00103Q00060B010700512Q013Q0004463Q00512Q010012FD003700633Q0020140038000700862Q000E0137000200020026250037003F2Q0100640004463Q003F2Q012Q001200375Q0010150007008600370012FD003700643Q0020C400370037008700202Q0038000700864Q003900366Q00370039000100122Q003700633Q00202Q0038000700884Q00370002000200262Q0037004B2Q0100640004463Q004B2Q012Q001200375Q0010150007008800370012FD003700643Q00206B00370037008700202Q0038000700884Q003900366Q00370039000100044Q00552Q012Q0052003700163Q00128D003800894Q0016003900014Q002E0037003900010006100137001B000100092Q00523Q000A4Q00523Q000B4Q00523Q00254Q00523Q00164Q00523Q000D4Q00523Q002C4Q00523Q002A4Q00523Q000F4Q00523Q00103Q0006100138001C000100032Q00523Q000B4Q00523Q00374Q00523Q00173Q0006100139001D000100162Q00523Q00104Q00523Q000B4Q00523Q00254Q00523Q00164Q00523Q000A4Q00523Q002A4Q00523Q00114Q00523Q00044Q00523Q00194Q00523Q00144Q00523Q00134Q00523Q00154Q00523Q00374Q00523Q001A4Q00523Q00354Q00523Q00224Q00523Q00184Q00523Q001E4Q00523Q00234Q00523Q00344Q00523Q002E4Q00523Q00123Q000610013A001E0001000A2Q00523Q00104Q00523Q00114Q00523Q00124Q00523Q00354Q00523Q002C4Q00523Q000E4Q00523Q000B4Q00523Q00254Q00523Q002F4Q00523Q00163Q000610013B001F000100032Q00523Q000A4Q00523Q000F4Q00523Q00063Q000610013C0020000100012Q00523Q00173Q002070003D0008008A00122Q003F008B6Q003D003F000100202Q003D0008008D4Q003F3Q000400302Q003F008E008F00302Q003F0090001300302Q003F0091009200061001400021000100042Q00523Q003C4Q00523Q000A4Q00523Q00394Q00523Q003A3Q001074003F009300404Q003D003F000200102Q000C008C003D00202Q003D0008008D4Q003F3Q000400302Q003F008E0095003005013F00900017003005013F0091009600061001400022000100012Q00523Q000A3Q001074003F009300404Q003D003F000200102Q000C0094003D00202Q003D000800974Q003F3Q000200302Q003F008E009800061001400023000100012Q00523Q00383Q001012013F009300404Q003D003F000100202Q003D000800974Q003F3Q000200302Q003F008E009900061001400024000100022Q00523Q000B4Q00523Q00173Q0010CB003F009300404Q003D003F000100202Q003D0008008A00122Q003F009A6Q003D003F00014Q003D001C6Q003D0001000200202Q003E0008009C4Q00403Q000600302Q0040008E009D2Q00490041003D3Q000E02002E00C12Q0100410004463Q00C12Q010006DA004100C42Q01003D0004463Q00C42Q012Q0012004100013Q00128D0042009F4Q003C0041000100010010150040009E00412Q001200415Q001015004000A00041003005014000A100170030050140009100A200061001410025000100032Q00523Q000A4Q00523Q000B4Q00523Q000C3Q0010F20040009300414Q003E0040000200102Q000C009B003E00202Q003E000800A400122Q004000A53Q00202Q0041000A00144Q004100413Q000E2Q002E00DD2Q0100410004463Q00DD2Q010012FD004100643Q0020C60041004100A600202Q0042000A001400122Q004300A76Q00410043000200062Q004100DE2Q0100010004463Q00DE2Q0100128D004100A84Q00D40040004000412Q0085003E0040000200102Q000C00A3003E00202Q003E0008008A00122Q004000A96Q003E0040000100202Q003E0008009C4Q00403Q000600302Q0040008E00AB4Q0041003D3Q000E2Q002E00EC2Q0100410004463Q00EC2Q010006DA004100EF2Q01003D0004463Q00EF2Q012Q0012004100013Q00128D0042009F4Q003C0041000100010010150040009E00410020140041000A00180006EE004100F42Q0100010004463Q00F42Q012Q001200415Q001015004000A00041003005014000A100170030050140009100AC00061001410026000100022Q00523Q000A4Q00523Q000B3Q0010740040009300414Q003E0040000200102Q000C00AA003E00202Q003E0008008D4Q00403Q000400302Q0040008E00AE0020140041000A00190010150040009000410030050140009100AF00061001410027000100012Q00523Q000A3Q0010740040009300414Q003E0040000200102Q000C00AD003E00202Q003E000800974Q00403Q000200302Q0040008E00B000061001410028000100052Q00523Q000B4Q00523Q00174Q00523Q003D4Q00523Q001C4Q00523Q000C3Q0010320040009300414Q003E0040000100202Q003E0008008A00122Q004000B16Q003E0040000100202Q003E0008008D4Q00403Q000400302Q0040008E00B300302Q00400090001700302Q0040009100B400061001410029000100012Q00523Q000A3Q0010F70040009300414Q003E0040000200102Q000C00B2003E00202Q003E000800A400122Q004000B66Q003E0040000200102Q000C00B5003E00202Q003E000800974Q00403Q000200302Q0040008E00B70006100141002A000100032Q00523Q000A4Q00523Q00174Q00523Q000C3Q0010120140009300414Q003E0040000100202Q003E000800974Q00403Q000200302Q0040008E00B80006100141002B000100032Q00523Q000A4Q00523Q000C4Q00523Q00173Q00101C0040009300414Q003E0040000100202Q003E0008008A00122Q004000B96Q003E0040000100202Q003E0008009C4Q00403Q000500302Q0040008E00BB4Q004100023Q00122Q004200233Q00128D004300BC4Q003C0041000200010010150040009E00412Q0012004100013Q0020140042000A00222Q003C004100010001001015004000A000410030050140009100BD0006100141002C000100032Q00523Q000A4Q00523Q000B4Q00523Q00163Q0010740040009300414Q003E0040000200102Q000C00BA003E00202Q003E0008009C4Q00403Q000500302Q0040008E00BF2Q0012004100033Q00128D004200C03Q00128D0043003B3Q00128D004400C14Q003C0041000300010010150040009E00412Q0012004100013Q0020140042000A003A2Q003C004100010001001015004000A000410030050140009100C20006100141002D000100042Q00523Q000A4Q00523Q002F4Q00523Q002E4Q00523Q00163Q0010740040009300414Q003E0040000200102Q000C00BE003E00202Q003E000800C34Q00403Q000200302Q004000C400C5003005014000C600C72Q002E003E00400001002070003E0008008A00122Q004000C86Q003E0040000100202Q003E0008008D4Q00403Q000400302Q0040008E00CA00302Q00400090001300302Q0040009100CB0006100141002E000100022Q00523Q000A4Q00523Q003B3Q0010740040009300414Q003E0040000200102Q000C00C9003E00202Q003E000800974Q00403Q000200302Q0040008E00CC0006100141002F000100052Q00523Q00034Q00523Q001A4Q00523Q000A4Q00523Q003B4Q00523Q00173Q0010120140009300414Q003E0040000100202Q003E000800CE4Q00403Q000600302Q0040008E00CF2Q0012004100023Q00128D0042001C3Q00128D004300D14Q003C004100020001001015004000D00041003005014000D2001C00300501400090005A0030050140009100D300061001410030000100022Q00523Q000A4Q00523Q003B3Q0010670040009300414Q003E0040000200102Q000C00CD003E00122Q003E00063Q00202Q003E003E0007000610013F0031000100062Q00523Q000A4Q00523Q003A4Q00523Q00094Q00523Q000B4Q00523Q000C4Q00523Q003B3Q001015003E00D4003F0012FD003E00063Q002014003E003E0007000610013F0032000100042Q00523Q000A4Q00523Q00104Q00523Q003A4Q00523Q000C3Q001015003E00D5003F2Q0052003E00174Q0031013F3Q000300302Q003F00C400D600302Q003F00C600D700302Q003F00D800D94Q003E000200010012FD003E00DA3Q00128D003F00DB4Q0073003E000200012Q00B23Q00013Q00333Q00053Q0003093Q0044656275674D6F6465030C3Q005B466F726765204661726D5D03013Q002003043Q007761726E03053Q007072696E7402144Q00AB00025Q0020140002000200010006EE00020005000100010004463Q000500012Q00B23Q00013Q00128D000200024Q004D000300023Q00122Q000400036Q00058Q00030003000500062Q0001001000013Q0004463Q001000010012FD000400044Q0052000500034Q00730004000200010004463Q001300010012FD000400054Q0052000500034Q00730004000200012Q00B23Q00017Q00023Q0003083Q005261796669656C6403063Q004E6F74696679010E4Q00AB00015Q00060B2Q01000500013Q0004463Q000500012Q00AB00015Q00201400010001000100060B2Q01000D00013Q0004463Q000D000100201400020001000200060B0102000D00013Q0004463Q000D00010020220002000100022Q005200046Q002E0002000400012Q00B23Q00017Q00053Q0003043Q006773756203043Q0025642B24034Q00030C3Q005E25732A282E2D2925732A2403023Q002531010A3Q00202900013Q000100122Q000300023Q00122Q000400036Q00010004000200202Q00010001000100122Q000300043Q00122Q000400056Q0001000400024Q000100028Q00017Q00053Q00030B3Q004C6F63616C506C61796572030F3Q004765744C6976696E67466F6C646572030E3Q0046696E6446697273744368696C6403063Q004C6976696E6703043Q004E616D65001A4Q00AB7Q0020145Q00010006EE3Q0006000100010004463Q000600012Q001D2Q0100014Q0047000100023Q0012FD000100023Q00060B2Q01000D00013Q0004463Q000D00010012FD000100024Q00BE0001000100020006EE00010011000100010004463Q001100012Q00AB000100013Q00202200010001000300128D000300044Q001A00010003000200060B2Q01001700013Q0004463Q0017000100202200020001000300201400043Q00052Q0006000200044Q008B00026Q001D010200024Q0047000200024Q00B23Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403063Q00506172656E74010E3Q0006DC0001000500013Q0004463Q0005000100202200013Q000100128D000300024Q001A00010003000200060B2Q01000B00013Q0004463Q000B000100201400020001000300060B0102000B00013Q0004463Q000B00012Q0047000100024Q001D010200024Q0047000200024Q00B23Q00017Q00013Q0003013Q005801083Q00201400013Q000100201400023Q00010006C500010005000100020004463Q000500012Q00ED00016Q0016000100014Q0047000100024Q00B23Q00017Q00123Q00030E3Q0046696E6446697273744368696C6403063Q004C6976696E6703053Q007061697273030A3Q00476574506C617965727303043Q004E616D6503053Q006C6F7765722Q01030B3Q00446973706C61794E616D65030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03083Q0048756D616E6F696403093Q00436861726163746572034Q0003053Q007461626C6503043Q0066696E6403063Q00696E7365727403043Q00736F727400554Q00F19Q0000015Q00202Q00010001000100122Q000300026Q0001000300024Q00025Q00122Q000300036Q000400013Q00202Q0004000400044Q000400056Q00033Q000500044Q001400010020140008000700050020F90008000800064Q00080002000200202Q00020008000700202Q00080007000800202Q0008000800064Q00080002000200202Q00020008000700067F0003000C000100020004463Q000C000100060B2Q01004F00013Q0004463Q004F00010012FD000300033Q0020220004000100092Q0078000400054Q001E01033Q00050004463Q004D000100202200080007000A00128D000A000B4Q001A0008000A000200060B0108004D00013Q0004463Q004D000100202200080007000100128D000A000C4Q001A0008000A000200060B0108004D00013Q0004463Q004D00012Q00AB000800023Q0020280109000700054Q00080002000200202Q0009000800064Q0009000200024Q0009000200094Q000A5Q00122Q000B00036Q000C00013Q00202Q000C000C00044Q000C000D6Q000B3Q000D00044Q003900010020140010000F000D0006EB00100039000100070004463Q003900012Q0016000A00013Q0004463Q003B000100067F000B0034000100020004463Q003400010026250008004D0001000E0004463Q004D00010012FD000B000F3Q00202B010B000B00104Q000C8Q000D00086Q000B000D000200062Q000B004D000100010004463Q004D00010006EE0009004D000100010004463Q004D00010006EE000A004D000100010004463Q004D00010012FD000B000F3Q002014000B000B00112Q0052000C6Q0052000D00084Q002E000B000D000100067F0003001D000100020004463Q001D00010012FD0003000F3Q0020210003000300124Q00048Q0003000200016Q00028Q00017Q000B3Q00030B3Q005A6F6E65456E61626C6564030A3Q005A6F6E6543656E74657203013Q005803083Q005A6F6E654C65667403093Q005A6F6E65526967687403013Q005903083Q005A6F6E65446F776E03063Q005A6F6E65557003013Q005A03093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B01364Q00AB00015Q0020140001000100010006EE00010006000100010004463Q000600012Q0016000100014Q0047000100024Q00AB00015Q0020A000010001000200202Q00023Q000300202Q0003000100034Q00045Q00202Q0004000400044Q00030003000400062Q00030032000100020004463Q0032000100201400023Q000300201E0003000100034Q00045Q00202Q0004000400054Q00030003000400062Q00020032000100030004463Q0032000100201400023Q00060020E40003000100064Q00045Q00202Q0004000400074Q00030003000400062Q00030032000100020004463Q0032000100201400023Q000600201E0003000100064Q00045Q00202Q0004000400084Q00030003000400062Q00020032000100030004463Q0032000100201400023Q00090020E40003000100094Q00045Q00202Q00040004000A4Q00030003000400062Q00030032000100020004463Q0032000100201400023Q00090020540003000100094Q00045Q00202Q00040004000B4Q00030003000400062Q00020002000100030004463Q003300012Q00ED00026Q0016000200014Q0047000200024Q00B23Q00017Q00103Q0003063Q00506172656E74030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403103Q0048756D616E6F6964522Q6F7450617274030A3Q0043616E436F2Q6C6964652Q0103063Q004865616C7468028Q0003063Q004C6976696E67030C3Q0053656C65637465644D6F627303043Q004E616D6503053Q00706169727303093Q00426C61636B6C69737403123Q0049676E6F7265496E76756C6E657261626C65030C3Q00496E76756C6E657261626C6503083Q00506F736974696F6E01873Q00060B012Q000500013Q0004463Q0005000100201400013Q00010006EE00010007000100010004463Q000700012Q001600016Q0047000100023Q00202200013Q000200126D000300036Q00010003000200202Q00023Q000200122Q000400046Q00020004000200062Q0002001100013Q0004463Q001100010006EE00010013000100010004463Q001300012Q001600036Q0047000300023Q00201400030002000100060B0103001900013Q0004463Q001900010020140003000100010006EE0003001B000100010004463Q001B00012Q001600036Q0047000300023Q0020140003000200050026AC00030023000100060004463Q0023000100201400030001000700262101030023000100080004463Q002300012Q001600036Q0047000300023Q00201400030001000700262101030028000100080004463Q002800012Q001600036Q0047000300024Q00AB00035Q00202200030003000200128D000500094Q001A00030005000200060B0103003100013Q0004463Q0031000100201400043Q00010006C500040033000100030004463Q003300012Q001600046Q0047000400024Q00AB000400013Q00201400040004000A00060B0104004F00013Q0004463Q004F00012Q00AB000400013Q00201400040004000A2Q0049000400043Q000E020008004F000100040004463Q004F00012Q00AB000400023Q00209B00053Q000B4Q0004000200024Q00055Q00122Q0006000C6Q000700013Q00202Q00070007000A4Q00060002000800044Q004900010006EB000A0049000100040004463Q004900012Q0016000500013Q0004463Q004B000100067F00060045000100020004463Q004500010006EE0005004F000100010004463Q004F00012Q001600066Q0047000600024Q00AB000400013Q00201400040004000D00060B0104006600013Q0004463Q006600012Q00AB000400013Q00201400040004000D2Q0049000400043Q000E0200080066000100040004463Q006600012Q00AB000400023Q0020AA00053Q000B4Q00040002000200122Q0005000C6Q000600013Q00202Q00060006000D4Q00050002000700044Q006400010006EB00090064000100040004463Q006400012Q0016000A6Q0047000A00023Q00067F00050060000100020004463Q006000012Q00AB000400013Q00201400040004000E00060B0104007800013Q0004463Q0078000100202200043Q000200128D0006000F4Q001A0004000600020006EE00040074000100010004463Q007400010006DC00040074000100010004463Q0074000100202200040001000200128D0006000F4Q001A00040006000200060B0104007800013Q0004463Q007800012Q001600056Q0047000500023Q0020140004000200010006EE0004007D000100010004463Q007D00012Q001600046Q0047000400024Q00AB000400033Q0020140005000200102Q000E0104000200020006EE00040084000100010004463Q008400012Q001600046Q0047000400024Q0016000400014Q0047000400024Q00B23Q00017Q00043Q0003043Q007469636B029A5Q99C93F030E3Q0046696E6446697273744368696C6403063Q004C6976696E6700143Q0012FD3Q00014Q00BE3Q000100022Q00AB00015Q00060B2Q01000B00013Q0004463Q000B00012Q00AB000100014Q00142Q013Q00010026810001000B000100020004463Q000B00012Q00AB00016Q0047000100024Q00113Q00014Q00FB000100023Q00202Q00010001000300122Q000300046Q0001000300024Q00018Q00018Q000100028Q00017Q000F3Q00030F3Q005072696F72697479456E61626C6564030C3Q0053656C65637465644D6F6273027Q004003063Q00506172656E7403043Q004E616D65030D3Q004D6F625072696F726974696573028Q0003053Q00706169727303083Q00506F736974696F6E030B3Q004765744368696C6472656E03093Q004D61676E697475646503093Q004661726D52616E676503063Q00737472696E6703063Q00666F726D6174031C3Q0020466F756E64206869676865722050206D6F623A202573285025642901754Q00AB00015Q0020140001000100010006EE00010006000100010004463Q000600012Q001D2Q0100014Q0047000100024Q00AB00015Q0020140001000100022Q0049000100013Q0026810001000D000100030004463Q000D00012Q001D2Q0100014Q0047000100023Q00060B012Q001200013Q0004463Q0012000100201400013Q00040006EE00010014000100010004463Q001400012Q001D2Q0100014Q0047000100024Q00AB000100013Q00201400023Q00052Q000E2Q01000200020006EE0001001B000100010004463Q001B00012Q001D010200024Q0047000200024Q00AB00025Q0020140002000200062Q003F0002000200010006EE00020021000100010004463Q0021000100128D000200073Q00128D000300073Q00129D000400086Q00055Q00202Q0005000500064Q00040002000600044Q002A00010006B40003002A000100080004463Q002A00012Q0052000300083Q00067F00040027000100020004463Q002700010006AD00030030000100020004463Q003000012Q001D010400044Q0047000400024Q00AB000400024Q00340004000100024Q000500036Q000600046Q00050002000200062Q00050039000100010004463Q003900012Q001D010600064Q0047000600023Q0020140006000500092Q00AB000700044Q00BE0007000100020006EE00070040000100010004463Q004000012Q001D010800084Q0047000800023Q00202200080007000A2Q000201080002000200122Q000900086Q000A5Q00202Q000A000A00064Q00090002000B00044Q007000010006B4000200700001000D0004463Q007000010012FD000E00084Q0052000F00085Q00010E000200100004463Q006E00012Q00AB001300054Q0052001400124Q000E01130002000200060B0113006E00013Q0004463Q006E00010006C50012006E000100040004463Q006E00012Q00AB001300013Q0020140014001200052Q000E0113000200020006EB0013006E0001000C0004463Q006E00012Q00AB001400034Q0052001500124Q000E01140002000200060B0114006E00013Q0004463Q006E00010020140015001400092Q003800150015000600202Q00150015000B4Q00165Q00202Q00160016000C00062Q0015006E000100160004463Q006E00012Q00AB001600063Q0012E70017000D3Q00202Q00170017000E00122Q0018000F6Q0019000C6Q001A000D6Q0017001A6Q00163Q00014Q001200023Q00067F000E004D000100020004463Q004D000100067F00090047000100020004463Q004700012Q001D010900094Q0047000900024Q00B23Q00017Q00193Q0003083Q00506F736974696F6E030B3Q004765744368696C6472656E03053Q00706169727303093Q004D61676E697475646503093Q004661726D52616E676503043Q004E616D6503053Q007461626C6503063Q00696E736572742Q033Q006E706303043Q0064697374030D3Q004D6F625072696F726974696573030F3Q005072696F72697479456E61626C6564030C3Q0053656C65637465644D6F6273028Q0003063Q0069706169727303083Q007072696F7269747903073Q006D6F625479706503043Q00736F727403043Q006D61746803043Q006875676503063Q00737472696E6703063Q00666F726D617403253Q00205072696F72697479204D6F623A2025732028503A2564292028252E316620737475647329032C3Q00204E6F207072696F72697479206D6F627320617661696C61626C652C2066612Q6C696E67206261636B3Q2E031E3Q002054617267657420466F756E643A2025732028252E31662073747564732900B64Q00659Q003Q000100024Q000100016Q00028Q00010002000200062Q00010009000100010004463Q000900012Q001D010200024Q0047000200023Q0020140002000100012Q00AB000300024Q00BE0003000100020006EE00030010000100010004463Q001000012Q001D010400044Q0047000400023Q0020220004000300022Q00FC0004000200024Q00055Q00122Q000600036Q000700046Q00060002000800044Q003900012Q00AB000B00034Q0052000C000A4Q000E010B0002000200060B010B003900013Q0004463Q003900010006C5000A003900013Q0004463Q003900012Q00AB000B00014Q0052000C000A4Q000E010B0002000200060B010B003900013Q0004463Q00390001002014000C000B00012Q0038000C000C000200202Q000C000C00044Q000D00043Q00202Q000D000D000500062Q000C00390001000D0004463Q003900012Q00AB000D00053Q002014000E000A00062Q000E010D000200022Q003F000E0005000D0006EE000E0032000100010004463Q003200012Q0012000E6Q00C00005000D000E0012FD000E00073Q0020BB000E000E00084Q000F0005000D4Q00103Q000200102Q00100009000A00102Q0010000A000C4Q000E0010000100067F00060017000100020004463Q001700012Q001600065Q00129D000700036Q000800043Q00202Q00080008000B4Q00070002000900044Q004300012Q0016000600013Q0004463Q0045000100067F00070041000100010004463Q004100012Q00AB000700043Q00201400070007000C00060B0107009400013Q0004463Q0094000100060B0106009400013Q0004463Q009400012Q00AB000700043Q00201400070007000D2Q0049000700073Q000E02000E0094000100070004463Q009400012Q001200075Q00129D0008000F6Q000900043Q00202Q00090009000D4Q00080002000A00044Q006300012Q00AB000D00043Q002014000D000D000B2Q003F000D000D000C0006EE000D005C000100010004463Q005C000100128D000D000E3Q0012FD000E00073Q002042000E000E00084Q000F00076Q00103Q000200102Q00100010000D00102Q00100011000C4Q000E0010000100067F00080056000100020004463Q005600010012FD000800073Q0020140008000800122Q0052000900073Q00020B000A6Q00C80008000A000100122Q0008000F6Q000900076Q00080002000A00044Q008F0001002014000D000C00112Q003F000D0005000D00060B010D008F00013Q0004463Q008F00012Q0049000E000D3Q000E02000E008F0001000E0004463Q008F00012Q001D010E000E3Q00127B000F00133Q00202Q000F000F001400122Q0010000F6Q0011000D6Q00100002001200044Q0081000100201400150014000A0006B4001500810001000F0004463Q00810001002014000F0014000A002014000E0014000900067F0010007C000100020004463Q007C000100060B010E008F00013Q0004463Q008F00012Q00AB001000063Q0012BD001100153Q00202Q00110011001600122Q001200173Q00202Q0013000C001100202Q0014000C00104Q0015000F6Q001100156Q00103Q00014Q000E00023Q00067F0008006E000100020004463Q006E00012Q00AB000800063Q00128D000900184Q00730008000200012Q001D010700073Q00127B000800133Q00202Q00080008001400122Q000900036Q000A00056Q00090002000B00044Q00A600010012FD000E000F4Q0052000F000D5Q00010E000200100004463Q00A4000100201400130012000A0006B4001300A4000100080004463Q00A4000100201400080012000A00201400070012000900067F000E009F000100020004463Q009F000100067F0009009B000100020004463Q009B000100060B010700B400013Q0004463Q00B400012Q00AB000900063Q001213010A00153Q00202Q000A000A001600122Q000B00196Q000C00053Q00202Q000D000700064Q000C000200024Q000D00086Q000A000D6Q00093Q00012Q0047000700024Q00B23Q00013Q00013Q00013Q0003083Q007072696F7269747902083Q00201400023Q000100201400030001000100062F01030005000100020004463Q000500012Q00ED00026Q0016000200014Q0047000200024Q00B23Q00017Q00053Q00030D3Q0043752Q72656E7454617267657403063Q00506172656E74030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403063Q004865616C746800164Q00AB7Q0020145Q000100060B012Q000700013Q0004463Q0007000100201400013Q00020006EE00010009000100010004463Q000900012Q001D2Q0100014Q0047000100023Q00202200013Q000300128D000300044Q001A00010003000200060B2Q01001100013Q0004463Q001100010020140002000100020006EE00020013000100010004463Q001300012Q001D010200024Q0047000200023Q0020140002000100052Q0047000200024Q00B23Q00017Q00233Q00030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D6503043Q007469636B030D3Q0043752Q72656E74546172676574026Q00F03F030C3Q0043752Q72656E745068617365028Q00030F3Q004C6F636B6564412Q7461636B506F730003063Q00737472696E6703063Q00666F726D617403233Q0020535455434B204C313A2050686173652072657365742028612Q7461636B733A25642903143Q00412Q7461636B7353696E636548504368616E6765027Q004003083Q00506F736974696F6E03093Q004D61676E697475646502FCA9F1D24D62503F032A3Q0020535455434B204C323A20546172676574206F7665726C61702C20736B692Q70696E6720676C6974636803043Q00556E6974030E3Q00537475636B446574656374696F6E030E3Q00476C6974636844697374616E636503063Q00434672616D652Q033Q006E6577032F3Q0020535455434B204C323A20476C69746368202B25642073747564732028612Q7461636B733A25642C204C3223256429030E3Q004C32412Q74656D7074436F756E74026Q00084003333Q0020535455434B204C324C333A20457363616C6174696E672061667465722033206661696C6564204C3220612Q74656D70747321030A3Q00466C696768744D6F646503053Q0042656C6F7703063Q0048656967687403073Q00566563746F7233026Q00104003263Q0020535455434B204C333A20466F7263652074656C65706F72742028612Q7461636B733A25642903043Q006D61746803053Q00666C2Q6F72018E4Q00E800015Q00102Q000100016Q00015Q00122Q000200036Q00020001000200102Q0001000200024Q000100016Q0001000100024Q000200026Q000300016Q0002000200024Q00035Q00202Q00030003000400062Q00040012000100030004463Q001200012Q00AB000400024Q0052000500034Q000E0104000200020006EE00020015000100010004463Q001500012Q00B23Q00013Q0026AC3Q0024000100050004463Q002400012Q00AB00055Q00301D0005000600074Q00055Q00302Q0005000800094Q000500033Q00122Q0006000A3Q00202Q00060006000B00122Q0007000C6Q00085Q00202Q00080008000D4Q000600086Q00053Q000100044Q008500010026AC3Q005D0001000E0004463Q005D000100060B0104005D00013Q0004463Q005D000100201400050004000F00201400060002000F2Q001401050005000600201400060005001000268100060033000100110004463Q003300012Q00AB000600033Q00128D000700124Q0016000800014Q002E0006000800010004463Q004C00010020140006000500130020EF00070002000F4Q000800043Q00202Q00080008001400202Q0008000800154Q0008000600084Q00070007000800122Q000800163Q00202Q0008000800174Q000900076Q0008000200020010150002001600082Q001F010800033Q00122Q0009000A3Q00202Q00090009000B00122Q000A00186Q000B00043Q00202Q000B000B001400202Q000B000B00154Q000C5Q00202Q000C000C000D4Q000D5Q002014000D000D00192Q00B10009000D4Q005300083Q00012Q00AB00066Q00A400075Q00202Q00070007001900202Q00070007000500102Q0006001900074Q00065Q00202Q000600060019000E2Q001A0085000100060004463Q008500012Q00AB000600033Q0012FF0007001B6Q0006000200014Q000600053Q00122Q0007001A6Q0006000200016Q00013Q00044Q008500010026AC3Q00850001001A0004463Q0085000100060B0104008500013Q0004463Q008500012Q00AB000500043Q00201400050005001C0026AC0005006A0001001D0004463Q006A00012Q00AB000500043Q00201400050005001E2Q00BF000500053Q0006EE0005006C000100010004463Q006C00012Q00AB000500043Q00201400050005001E00201400060004000F0012260107001F3Q00202Q00070007001700122Q000800076Q000900053Q00122Q000A00076Q0007000A00024Q00060006000700122Q000700163Q00202Q0007000700174Q000800066Q00070002000200102Q0002001600074Q00075Q00302Q0007000600204Q00075Q00302Q0007001900074Q000700033Q00122Q0008000A3Q00202Q00080008000B00122Q000900216Q000A5Q00202Q000A000A000D4Q0008000A6Q00073Q00012Q00AB00055Q0012FA000600223Q00202Q0006000600234Q00075Q00202Q00070007000D00202Q00070007000E4Q00060002000200102Q0005000D00066Q00017Q001E3Q00030E3Q00537475636B446574656374696F6E03073Q00456E61626C6564030D3Q0043752Q72656E74546172676574030C3Q004C617374546172676574485000030D3Q004C617374546172676574526566030E3Q004C61737454726176656C4C2Q6F6B03143Q00412Q7461636B7353696E636548504368616E6765028Q00030E3Q00537475636B436865636B54696D6503043Q007469636B030D3Q005265636F766572794C6576656C030E3Q004C32412Q74656D7074436F756E74030D3Q004C617374546172676574506F7303113Q004C617374546172676574506F7354696D65030A3Q00546F74616C4B692Q6C73026Q00F03F03083Q00506F736974696F6E03093Q004D61676E697475646503113Q00506F736974696F6E5468726573686F6C64030C3Q00506F736974696F6E54696D6503103Q004C6173745265636F7665727954696D6503103Q005265636F76657279432Q6F6C646F776E030B3Q005468726573686F6C644C33026Q000840030B3Q005468726573686F6C644C32030D3Q0054696D655468726573686F6C64026Q00F83F027Q0040030B3Q005468726573686F6C644C3100AA4Q00AB7Q0020145Q000100060B012Q000900013Q0004463Q000900012Q00AB7Q0020145Q00010020145Q00020006EE3Q000A000100010004463Q000A00012Q00B23Q00014Q00AB3Q00013Q0020145Q00030006EE3Q0019000100010004463Q001900012Q00AB000100013Q0030600001000400054Q000100013Q00302Q0001000600054Q000100013Q00302Q0001000700054Q000100013Q00302Q0001000800094Q000100013Q00302Q0001000A00096Q00014Q00AB000100024Q00BE0001000100020006EE0001001E000100010004463Q001E00012Q00B23Q00013Q0012FD0002000B4Q00BE0002000100022Q00AB000300013Q0020140003000300060006C50003003100013Q0004463Q003100012Q00AB000300013Q0010B80003000400014Q000300013Q00102Q000300066Q000300013Q00302Q0003000800094Q000300013Q00102Q0003000A00024Q000300013Q00302Q0003000C00094Q000300013Q00302Q0003000D00096Q00014Q00AB000300013Q0020140003000300040006B40001004F000100030004463Q004F00012Q00AB000300013Q0010170003000400014Q000300013Q00302Q0003000800094Q000300013Q00102Q0003000A00024Q000300013Q00302Q0003000C00094Q000300013Q00302Q0003000D00094Q000300013Q00302Q0003000E00054Q000300013Q00302Q0003000F000900262Q0001004E000100090004463Q004E00012Q00AB000300014Q003A000400013Q00202Q00040004001000202Q00040004001100102Q0003001000044Q000300013Q00302Q0003000400054Q000300013Q00302Q0003000600052Q00B23Q00014Q00AB00035Q0020DB0003000300014Q000400036Q00058Q00040002000200062Q0004007700013Q0004463Q007700010020140005000400122Q00AB000600013Q00201400060006000E0006EE00060060000100010004463Q006000012Q00AB000600013Q0010150006000E00052Q00AB000600013Q0010150006000F00020004463Q007700012Q00AB000600013Q00204F00060006000E4Q00060005000600202Q00060006001300202Q00070003001400062Q0007006C000100060004463Q006C00012Q00AB000700013Q0010150007000E00052Q00AB000700013Q0010150007000F00020004463Q007700012Q00AB000700013Q00201400070007000F2Q00140107000200070020140008000300150006AD00080077000100070004463Q007700012Q00AB000700043Q00128D000800114Q00730007000200012Q00AB000700013Q0010150007000F00022Q00AB000500014Q005D000600013Q00202Q00060006000800202Q00060006001100102Q0005000800064Q000500013Q00202Q00050005000A4Q0005000200054Q000600013Q00202Q0006000600164Q0006000200064Q00075Q00202Q00070007000100202Q00070007001700062Q00060088000100070004463Q008800012Q00B23Q00014Q00AB000600013Q0020140006000600080020140007000300180006AD00070091000100060004463Q009100012Q00AB000600043Q00128D000700194Q00730006000200010004463Q00A900012Q00AB000600013Q00201400060006000800201400070003001A00060500070005000100060004463Q009A000100201400060003001B00205B00060006001C0006AD0006009E000100050004463Q009E00012Q00AB000600043Q00128D0007001D4Q00730006000200010004463Q00A900012Q00AB000600013Q00201400060006000800201400070003001E00060500070004000100060004463Q00A6000100201400060003001B0006AD000600A9000100050004463Q00A900012Q00AB000600043Q00128D000700114Q00730006000200012Q00B23Q00017Q000E3Q0003043Q007469636B030B3Q00412Q7461636B44656C6179029A5Q99B93F028Q0003043Q006D61746803063Q0072616E646F6D026Q00D03F026Q00F03F03063Q00737472696E6703063Q00666F726D6174031B3Q005B412Q7461636B5D20232564202844656C61793A20252E3266732903053Q007063612Q6C03153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C00373Q0012B63Q00018Q000100024Q00015Q00202Q00010001000200062Q00010007000100010004463Q0007000100128D000100033Q0026810001000A000100040004463Q000A000100128D000100043Q0012FD000200053Q0020570002000200064Q00020001000200202Q0002000200074Q0002000100024Q000300016Q00033Q000300062Q00030014000100020004463Q001400012Q00B23Q00014Q00AB000300023Q0020B30003000300084Q000300028Q00016Q000300033Q00122Q000400093Q00202Q00040004000A00122Q0005000B6Q000600026Q000700026Q000400076Q00033Q000100122Q0003000C3Q00061001043Q000100032Q00AB3Q00044Q00AB3Q00054Q00AB3Q00034Q00730003000200012Q00AB000300064Q00BE00030001000200060B0103003400013Q0004463Q0034000100202200040003000D00128D0006000E4Q001A00040006000200060B0104003300013Q0004463Q003300010012FD0005000C3Q00061001060001000100012Q00523Q00044Q00730005000200012Q008E00046Q00AB000400074Q00BA0004000100012Q00B23Q00013Q00023Q000D3Q0003063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q005365727669636573030B3Q00542Q6F6C5365727669636503023Q005246030D3Q00542Q6F6C416374697661746564030C3Q00496E766F6B6553657276657203063Q00576561706F6E030C3Q004C617374542Q6F6C5761726E03043Q007469636B027Q0040032D3Q005B412Q7461636B5D20542Q6F6C53657276696365206D692Q73696E672C20736B692Q70696E6720696E766F6B6500294Q001F7Q00206Q000100206Q000200206Q000300206Q000400206Q000500064Q001500013Q0004463Q0015000100201400013Q000600060B2Q01001500013Q0004463Q0015000100201400013Q000600201400010001000700060B2Q01001500013Q0004463Q0015000100201400013Q000600205800010001000700202Q00010001000800122Q000300096Q00010003000100044Q002800012Q00AB000100013Q00201400010001000A00060B2Q01002000013Q0004463Q002000010012FD0001000B4Q00940001000100024Q000200013Q00202Q00020002000A4Q000100010002000E2Q000C0028000100010004463Q002800012Q00AB000100023Q0012100002000D6Q000300016Q0001000300014Q000100013Q00122Q0002000B6Q00020001000200102Q0001000A00022Q00B23Q00017Q00013Q0003083Q00416374697661746500044Q00AB7Q0020225Q00012Q00733Q000200012Q00B23Q00017Q00163Q00032F3Q00204D616769632043617270657420616C7265616479206578697374732C20736B692Q70696E67206372656174696F6E03083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D65030F3Q004661726D4D6167696343617270657403043Q0053697A6503073Q00566563746F7233026Q001840026Q00E03F030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C696465010003083Q0043616E546F75636803083Q0043616E517565727903063Q00506172656E74034A3Q00204D61676963204361727065742043524541544544207C2053697A653A203678302E357836207C20416E63686F7265643A2074727565207C2043616E436F2Q6C6964653A2066616C736503053Q007072696E74032A3Q005B466F726765204661726D5D204D61676963204361727065742043726561746564202853746174696329002B4Q00AB7Q00060B012Q000700013Q0004463Q000700012Q00AB3Q00013Q00128D000100014Q00733Q000200012Q00B23Q00013Q0012FD3Q00023Q0020E15Q000300122Q000100048Q000200029Q009Q0000304Q000500069Q0000122Q000100083Q00202Q00010001000300122Q000200093Q00122Q0003000A3Q00122Q000400096Q00010004000200104Q000700019Q0000304Q000B000C9Q0000304Q000D000E9Q0000304Q000F00109Q0000304Q001100109Q0000304Q001200109Q004Q000100023Q00104Q001300016Q00013Q00122Q000100146Q000200018Q0002000100124Q00153Q00122Q000100168Q000200016Q00017Q00153Q0003063Q00506172656E7403233Q004D6167696320436172706574206973206E696C212043612Q6E6F74207570646174652E032D3Q00522Q6F745061727420696E76616C6964212043612Q6E6F7420757064617465204D61676963204361727065742E03063Q00434672616D652Q033Q006E6577028Q00030B3Q0047686F73744F2Q6673657403093Q0044656275674D6F6465030C3Q005472616E73706172656E6379029A5Q99C93F026Q00F03F03043Q006D61746803063Q0072616E646F6D029A5Q99A93F03083Q00506F736974696F6E03063Q00737472696E6703063Q00666F726D617403343Q004D61676963436172706574207C20506F733A2028252E31662C20252E31662C20252E316629207C204F2Q667365743A20252E316603013Q005803013Q005903013Q005A014D4Q00AB00015Q00060B2Q01000700013Q0004463Q000700012Q00AB00015Q0020140001000100010006EE00010011000100010004463Q001100012Q00AB000100014Q00BA0001000100012Q00AB00015Q0006EE00010011000100010004463Q001100012Q00AB000100023Q00128D000200024Q0016000300014Q002E0001000300012Q00B23Q00014Q00AB00015Q0020140001000100012Q00AB000200033Q0006C500010019000100020004463Q001900012Q00AB00016Q00AB000200033Q00101500010001000200060B012Q001E00013Q0004463Q001E000100201400013Q00010006EE00010023000100010004463Q002300012Q00AB000100023Q00128D000200034Q0016000300014Q002E0001000300012Q00B23Q00013Q00201400013Q000400120E000200043Q00202Q00020002000500122Q000300066Q000400043Q00202Q00040004000700122Q000500066Q0002000500024Q0001000100024Q00025Q00102Q0002000400014Q000200043Q00202Q00020002000800062Q0002003500013Q0004463Q003500012Q00AB00025Q00300501020009000A0004463Q003700012Q00AB00025Q00300501020009000B2Q00AB000200043Q00201400020002000800060B0102004C00013Q0004463Q004C00010012FD0002000C3Q00201400020002000D2Q00BE0002000100020026810002004C0001000E0004463Q004C000100201400020001000F2Q00E0000300023Q00122Q000400103Q00202Q00040004001100122Q000500123Q00202Q00060002001300202Q00070002001400202Q0008000200154Q000900043Q00202Q0009000900074Q000400096Q00033Q00012Q00B23Q00017Q00053Q0003073Q0044657374726F7903173Q00204D61676963204361727065742044455354524F59454403053Q007072696E7403233Q005B466F726765204661726D5D204D61676963204361727065742044657374726F79656403313Q00204D61676963204361727065742077617320616C7265616479206E696C2C206E6F7468696E6720746F2064657374726F7900144Q00AB7Q00060B012Q001000013Q0004463Q001000012Q00AB7Q00201C014Q00016Q000200019Q009Q006Q00013Q00122Q000100026Q000200018Q0002000100124Q00033Q00122Q000100048Q0002000100044Q001300012Q00AB3Q00013Q00128D000100054Q00733Q000200012Q00B23Q00017Q00013Q00030D3Q0043752Q72656E7443616D65726100044Q00AB7Q0020145Q00012Q00473Q00024Q00B23Q00017Q000D3Q00030A3Q0043616D6572614D6F646503043Q004E6F6E6503123Q004F726967696E616C43616D6572615479706503113Q004F726967696E616C43616D657261526566030A3Q0043616D6572615479706503103Q0043616D657261436F2Q6E656374696F6E030A3Q00446973636F2Q6E6563740003163Q002043616D657261204D6F646520535441525445443A2003043Q00456E756D030A3Q0053637269707461626C65030D3Q0052656E6465725374652Q70656403073Q00436F2Q6E65637400384Q00AB7Q0020145Q00010026AC3Q0005000100020004463Q000500012Q00B23Q00014Q00AB3Q00014Q00BE3Q000100020006EE3Q000A000100010004463Q000A00012Q00B23Q00014Q00AB000100023Q00201400010001000300060B2Q01001200013Q0004463Q001200012Q00AB000100023Q0020140001000100040006C50001001700013Q0004463Q001700012Q00AB000100023Q00201400023Q00050010150001000300022Q00AB000100023Q001015000100044Q00AB000100023Q00201400010001000600060B2Q01002100013Q0004463Q002100012Q00AB000100023Q00207700010001000600202Q0001000100074Q0001000200014Q000100023Q00302Q0001000600082Q00AB000100033Q001269000200096Q00035Q00202Q0003000300014Q0002000200034Q00010002000100122Q0001000A3Q00202Q00010001000500202Q00010001000B00104Q000500014Q000100026Q000200043Q00202Q00020002000C00202Q00020002000D00061001043Q000100052Q00AB8Q00AB3Q00014Q00AB3Q00054Q00AB3Q00064Q00AB3Q00024Q001A0002000400020010150001000600022Q00B23Q00013Q00013Q001C3Q0003083Q004175746F4661726D030A3Q0043616D6572615479706503043Q00456E756D030A3Q0053637269707461626C65030D3Q0043752Q72656E74546172676574030C3Q0043616D657261486569676874030E3Q0043616D65726144697374616E6365030A3Q0043616D65726153696465030A3Q0043616D6572614D6F6465030A3Q004C6F636B54617267657403083Q00506F736974696F6E03063Q00434672616D65030A3Q004C2Q6F6B566563746F7203043Q004C657270029A5Q99C93F03073Q00566563746F72332Q033Q006E657703013Q0058028Q0003013Q005A03093Q004D61676E6974756465029A5Q99B93F03043Q00556E6974026Q00F0BF03063Q006C2Q6F6B4174030B3Q005269676874566563746F72030B3Q0046697865644F2Q66736574026Q00144000A04Q00AB7Q0020145Q00010006EE3Q0005000100010004463Q000500012Q00B23Q00014Q00AB3Q00014Q00BE3Q000100020006EE3Q000A000100010004463Q000A00012Q00B23Q00013Q00201400013Q00020012FD000200033Q0020140002000200020020140002000200040006C500010014000100020004463Q001400010012FD000100033Q0020140001000100020020140001000100040010153Q000200012Q00AB000100024Q00340001000100024Q000200036Q000300016Q00020002000200062Q0002001C000100010004463Q001C00012Q00B23Q00014Q00AB000300043Q00201400030003000500060B0103002400013Q0004463Q002400012Q00AB000300034Q00AB000400043Q0020140004000400052Q000E0103000200022Q00AB00045Q00206C0004000400064Q00055Q00202Q0005000500074Q00065Q00202Q0006000600084Q00075Q00202Q00070007000900262Q0007007D0001000A0004463Q007D000100060B0103006600013Q0004463Q0066000100201400070002000B00204B00080003000B00202Q00090002000C00202Q00090009000D4Q0009000900054Q00090007000900202Q000A0008000E4Q000C00093Q00122Q000D000F6Q000A000D00024Q000B0008000700122Q000C00103Q00202Q000C000C001100202Q000D000B001200122Q000E00133Q00202Q000F000B00144Q000C000F000200202Q000D000C0015000E2Q001600470001000D0004463Q00470001002014000D000C00170006EE000D004D000100010004463Q004D00010012FD000D00103Q00202D000D000D001100122Q000E00133Q00122Q000F00133Q00122Q001000186Q000D001000020012FD000E00103Q0020D1000E000E001100202Q000F000D001400122Q001000133Q00202Q0011000D00124Q001100116Q000E001100024Q000F000D00054Q000F0007000F00122Q001000103Q00202Q00100010001100122Q001100136Q001200043Q00122Q001300136Q0010001300024Q000F000F00104Q0010000E00064Q000F000F001000122Q0010000C3Q00202Q0010001000194Q0011000F6Q0012000A6Q00100012000200104Q000C001000044Q009F000100201400070002000C00208400070007000D00202Q00080002000C00202Q00080008001A00202Q00090002000B4Q000A000700054Q00090009000A00122Q000A00103Q00202Q000A000A001100122Q000B00136Q000C00043Q00122Q000D00136Q000A000D00024Q00090009000A4Q000A000800064Q00090009000A00122Q000A000C3Q00202Q000A000A00194Q000B00093Q00202Q000C0002000B4Q000A000C000200104Q000C000A00044Q009F00012Q00AB00075Q0020140007000700090026AC0007009F0001001B0004463Q009F000100201400070002000C00200301070007000D00202Q00080002000C00202Q00080008001A00202Q00090002000B4Q000A000700054Q00090009000A00122Q000A00103Q00202Q000A000A001100122Q000B00136Q000C00043Q00122Q000D00136Q000A000D00024Q00090009000A4Q000A000800064Q00090009000A00202Q000A0002000B00122Q000B00103Q00202Q000B000B001100122Q000C00133Q00122Q000D001C3Q00122Q000E00136Q000B000E00024Q000A000A000B00122Q000B000C3Q00202Q000B000B00194Q000C00096Q000D000A6Q000B000D000200104Q000C000B2Q00B23Q00017Q000B3Q0003103Q0043616D657261436F2Q6E656374696F6E030A3Q00446973636F2Q6E6563740003143Q002043616D657261204D6F64652053544F2Q50454403123Q004F726967696E616C43616D65726154797065030A3Q0043616D6572615479706503153Q002043616D65726120726573746F72656420746F3A2003083Q00746F737472696E6703043Q00456E756D03063Q00437573746F6D03113Q004F726967696E616C43616D65726152656600294Q00AB7Q0020145Q000100060B012Q000D00013Q0004463Q000D00012Q00AB7Q0020885Q000100206Q00026Q000200019Q0000304Q000100036Q00013Q00122Q000100048Q000200012Q00AB3Q00024Q00BE3Q0001000200060B012Q002400013Q0004463Q002400012Q00AB00015Q00201400010001000500060B2Q01002000013Q0004463Q002000012Q00AB00015Q00207E00010001000500104Q000600014Q000100013Q00122Q000200073Q00122Q000300083Q00202Q00043Q00064Q0003000200024Q0002000200034Q00010002000100044Q002400010012FD000100093Q00201400010001000600201400010001000A0010153Q000600012Q00AB00015Q0030052Q01000500032Q00AB00015Q0030052Q01000B00032Q00B23Q00017Q00093Q0003043Q007469636B026Q00E03F030E3Q0046696E6446697273744368696C64030D3Q00537061776E4C6F636174696F6E03113Q005361666548656967687444656661756C7403083Q00506F736974696F6E03093Q004D61676E697475646503103Q00537061776E436865636B526164697573030F3Q0053616665486569676874537061776E01203Q0012FD000100014Q00BE0001000100022Q00AB00025Q00060B0102000B00013Q0004463Q000B00012Q00AB000200014Q00140102000100020026810002000B000100020004463Q000B00012Q00AB00026Q0047000200024Q0011000100014Q003D000200023Q00202Q00020002000300122Q000400046Q0002000400024Q000300033Q00202Q00030003000500062Q0002001D00013Q0004463Q001D00010020140004000200062Q003800043Q000400202Q0004000400074Q000500033Q00202Q00050005000800062Q0004001D000100050004463Q001D00012Q00AB000400033Q0020140003000400092Q001100036Q0047000300024Q00B23Q00017Q000E3Q0003063Q0048656967687403103Q00486F72697A6F6E74616C4F2Q66736574028Q0003083Q00506F736974696F6E030A3Q00466C696768744D6F646503053Q0041626F766503013Q0059025Q00207CC003063Q00434672616D65030A3Q004C2Q6F6B566563746F7203013Q005A03013Q005803073Q00566563746F72332Q033Q006E657701264Q004E00015Q00202Q0001000100014Q00025Q00202Q00020002000200062Q00020007000100010004463Q0007000100128D000200033Q00201400033Q00042Q001D010400044Q00AB00055Q0020140005000500050026AC00050010000100060004463Q001000010020140005000300072Q00710004000500010004463Q001200010020140005000300072Q001401040005000100268100040015000100080004463Q0015000100128D000400083Q00201400053Q00090020E900050005000A00202Q00060005000B4Q00060006000200202Q00070005000C4Q000700076Q00070007000200122Q0008000D3Q00202Q00080008000E00202Q00090003000C4Q0009000900064Q000A00043Q00202Q000B0003000B4Q000B000B00074Q0008000B6Q00089Q0000017Q00683Q0003083Q00506F736974696F6E03293Q0020522Q4F5420504F534954494F4E204953204E614E212041626F7274696E67206D6F76656D656E742E032A3Q0020454E454D5920504F534954494F4E204953204E614E212041626F7274696E67206D6F76656D656E742E030A3Q0047686F737453702Q6564026Q11913F03073Q00566563746F72332Q033Q006E657703013Q0058028Q0003013Q005A03093Q004D61676E6974756465030C3Q0043752Q72656E745068617365027Q0040026Q000840026Q001040026Q003440030A3Q00466C696768744D6F646503053Q0042656C6F77030F3Q0042656C6F7744657363656E64696E6703133Q00446972656374436861736544697374616E636503013Q0059026Q001440026Q00F03F0100030D3Q00506C6174666F726D5374616E642Q0102CD5QCCF43F03063Q00737472696E6703063Q00666F726D617403313Q0020444952454354204348415345207C20646973743A252E3166203C202564207C20736B692Q70696E672050686173652031026Q002440026Q003E4003043Q006D6174682Q033Q00616273026Q00494003093Q0044656275674D6F646503063Q0072616E646F6D029A5Q99B93F033C3Q002042454C4F572044455343454E44207C20666C61743A252E3166207C20593A252E3166252E3166207C20737461792061742063752Q72656E7420585A03393Q002042454C4F5720534C494445207C20666C61743A252E3166207C20593A252E3166207C206D6F76696E6720746F20756E64657220656E656D79034Q00030A3Q0050313A4845494748545F03043Q00484947482Q033Q004C4F5703103Q0050323A454E454D595F4553434150454403153Q0020456E656D7920657363617065642120666C61743D03053Q00666C2Q6F72030A3Q002Q2043686173696E672103123Q0050333A485953544552455349535F4C4F434B026Q002E4003113Q0050343A4E4F545F504F534954494F4E4544030D3Q0050353A564552595F434C4F5345030F3Q0050353A4E4F524D414C5F454E545259030E3Q0050353A4B2Q45505F4445504C4F59029A5Q99A93F03013Q004E03323Q00205048415345207C2025642564207C20666C61743A252E316620646973743A252E3166207C20776173343A2573207C20257303163Q00412Q73656D626C794C696E65617256656C6F6369747903043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030F3Q004C6F636B6564412Q7461636B506F7300030D3Q0053702Q6564412Q70726F61636803043Q004C657270026Q66D63F03103Q00536B6970412Q7461636B4672616D657303083Q0044697374616E6365027B14AE47E17A943F03333Q0020542Q4F2046415220544F20412Q5441434B207C20646973743A252E3166203E20436F6E6669672E44697374616E63653A2564032C3Q00204E6F20776179706F696E742063616C63756C61746564202870686173653D30292E2041626F7274696E672E030D3Q0053616665747920417363656E74030A3Q00536B7920437275697365030A3Q004465706C6F796D656E7403063Q00412Q7461636B032A3Q002050686173652025643A202573207C20446973743A20252E3166207C20593A20252E31662Q20252E316603073Q00556E6B6E6F776E03083Q0053702Q656446617203093Q0053702Q65644E656172030B3Q0053702Q6564536C6F776D6F03043Q00556E69742Q033Q006D696E03083Q00496E7374616E636503083Q00426F64794779726F03093Q004D6178546F72717565024Q00652QCD4103013Q0050025Q0088C34003063Q00506172656E7403063Q00434672616D6503063Q006C2Q6F6B4174030A3Q004C2Q6F6B566563746F72034D3Q0020524F544154494F4E204445425547207C204C2Q6F6B446973743A20252E3166207C204C2Q6F6B5665633A2028252E32662C20252E32662C20252E326629207C204D6F64653A20434672616D6503273Q0020524F544154494F4E20534B492Q5045443A206C2Q6F6B4469737420742Q6F20736D612Q6C202803083Q00746F737472696E6703013Q002903163Q00526F746174696F6E446561645A6F6E6554726176656C030E3Q004C61737454726176656C4C2Q6F6B03013Q0044026Q005940023Q0020F56B0C4303103Q00526F746174696F6E446561645A6F6E65030E3Q004C6173744C2Q6F6B546172676574033E3Q0020504F534954494F4E204F564552464C4F572044455445435445442120536B692Q70696E67206672616D652028252E31652C20252E31652C20252E31652903263Q00204E614E20504F534954494F4E2044455445435445442120536B692Q70696E67206672616D650401033Q00D000048Q00058Q00040002000100202Q00043Q000100202Q0005000200014Q000600016Q000700046Q00060002000200062Q0006000F000100010004463Q000F00012Q00AB000600023Q00128D000700024Q0016000800014Q002E0006000800012Q00B23Q00014Q00AB000600014Q0052000700054Q000E0106000200020006EE00060019000100010004463Q001900012Q00AB000600023Q00128D000700034Q0016000800014Q002E0006000800012Q00B23Q00014Q00AB000600034Q0079000700026Q0006000200024Q000700046Q000800046Q0007000200024Q000800053Q00202Q00080008000400062Q00090024000100030004463Q0024000100128D000900054Q00D800080008000900123B000900063Q00202Q00090009000700202Q000A0006000800202Q000B000400084Q000A000A000B00122Q000B00093Q00202Q000C0006000A00202Q000D0004000A4Q000C000C000D4Q0009000C000200202Q00090009000B4Q000A0006000400202Q000A000A000B4Q000B000B6Q000C5Q00122Q000D00096Q000E00063Q00202Q000E000E000C00262Q000E003A0001000D0004463Q003A00012Q00ED000E6Q0016000E00014Q00AB000F00063Q002014000F000F000C002625000F00440001000E0004463Q004400012Q00AB000F00063Q002014000F000F000C002625000F00440001000F0004463Q004400012Q00ED000F6Q0016000F00013Q00060B010F004C00013Q0004463Q004C0001000E020010004C000100090004463Q004C00012Q0016000F6Q00AB001000063Q0030050110000C00092Q00AB001000053Q0020140010001000110026AC00100053000100120004463Q005300012Q00AB001000063Q0020140010001000130004463Q005500012Q00ED00106Q0016001000014Q00AB001100053Q002014001100110014000605000A0002000100110004463Q005A00012Q00ED00116Q0016001100013Q0006EE00100077000100010004463Q007700010006EE00110077000100010004463Q007700010006EE000E0077000100010004463Q007700010006EE000F0077000100010004463Q007700010020140012000400150020A10013000700160006B400120077000100130004463Q0077000100128D000D00174Q00F0001200063Q00302Q00120013001800122Q001200063Q00202Q00120012000700202Q0013000400084Q001400073Q00202Q00150004000A4Q0012001500024Q000B00123Q00202Q00120001001900062Q00120075000100010004463Q007500010030052Q010019001A00205B00080008001B0004463Q00E12Q0100060B0111009100013Q0004463Q009100010006EE000E0091000100010004463Q009100010006EE000F0091000100010004463Q009100010020140012000400150020A10013000700160006B400120091000100130004463Q0091000100128D000D000E4Q0052000B00063Q0020140012000100190006EE00120087000100010004463Q008700010030052Q010019001A2Q00AB001200023Q0012A60013001C3Q00202Q00130013001D00122Q0014001E6Q0015000A6Q001600053Q00202Q0016001600144Q001300166Q00123Q000100044Q00E12Q010006EE000E0097000100010004463Q009700010020140012000400150020A10013000700160006AD001300B2000100120004463Q00B20001000E02001F00B2000100090004463Q00B200010006EE000F00B2000100010004463Q00B2000100128D000D000D4Q0052001200073Q0020140013000400150020A10014000700160006B4001300A2000100140004463Q00A2000100206800120007000D0012FD001300063Q00200401130013000700202Q0014000600084Q001500123Q00202Q00160006000A4Q0013001600024Q000B00133Q00262Q000900AC000100200004463Q00AC00012Q00ED000C6Q0016000C00013Q0020140013000100190006EE001300E12Q0100010004463Q00E12Q010030052Q010019001A0004463Q00E12Q012Q00AB001200063Q00201400120012000C002625001200B70001000F0004463Q00B700012Q00ED00126Q0016001200014Q00AB001300053Q002014001300130011002625001300BD000100120004463Q00BD00012Q00ED00136Q0016001300014Q001600145Q00060B011300192Q013Q0004463Q00192Q0100201400150002000100204300150015001500202Q00160002000100122Q001700213Q00202Q00170017002200202Q00180004001500202Q0019000600154Q0018001800194Q00170002000200262Q001700CD000100160004463Q00CD00012Q00ED00176Q0016001700013Q00201400180004001500201400190006001500206800190019001600062F011900D4000100180004463Q00D400012Q00ED00186Q0016001800013Q00060B011700DB00013Q0004463Q00DB0001002681000900DB000100160004463Q00DB00012Q00AB001900063Q00300501190013001800060B011800FE00013Q0004463Q00FE0001002681000900FE000100230004463Q00FE000100128D000D000E4Q00D7001900063Q00302Q00190013001A00122Q001900063Q00202Q00190019000700202Q001A0004000800202Q001B0006001500202Q001C0004000A4Q0019001C00024Q000B00196Q000C8Q001400016Q001900053Q00202Q00190019002400062Q001900192Q013Q0004463Q00192Q010012FD001900213Q0020140019001900252Q00BE001900010002002681001900192Q0100260004463Q00192Q012Q00AB001900023Q0012F3001A001C3Q00202Q001A001A001D00122Q001B00276Q001C00093Q00202Q001D0004001500202Q001E000600154Q001A001E6Q00193Q000100044Q00192Q0100060B011700192Q013Q0004463Q00192Q01000E02000E00192Q0100090004463Q00192Q0100128D000D000E4Q006F001900063Q00302Q00190013001A4Q000B00066Q000C00016Q001400016Q001900053Q00202Q00190019002400062Q001900192Q013Q0004463Q00192Q010012FD001900213Q0020140019001900252Q00BE001900010002002681001900192Q0100260004463Q00192Q012Q00AB001900023Q001224011A001C3Q00202Q001A001A001D00122Q001B00286Q001C00093Q00202Q001D000400154Q001A001D6Q00193Q00010006EE001400E12Q0100010004463Q00E12Q010012FD001500213Q00202700150015002200202Q00160004001500202Q0017000600154Q0016001600174Q00150002000200262Q001500242Q0100160004463Q00242Q012Q00ED00166Q0016001600013Q00128D0017000F3Q00128D001800294Q001600195Q00060B011300322Q013Q0004463Q00322Q01002014001A00040015002014001B00060015002068001B001B001F00062F011B00302Q01001A0004463Q00302Q012Q00ED00196Q0016001900013Q0004463Q00392Q01002014001A00040015002014001B000600150020A1001B001B001F00062F011A00382Q01001B0004463Q00382Q012Q00ED00196Q0016001900013Q00060B011900452Q013Q0004463Q00452Q0100128D000D000E3Q00128D001A002A3Q00060B011300422Q013Q0004463Q00422Q0100128D001B002B3Q0006EE001B00432Q0100010004463Q00432Q0100128D001B002C4Q00D40018001A001B0004463Q00742Q0100060B011200562Q013Q0004463Q00562Q01000E02001F00562Q0100090004463Q00562Q0100128D000D00173Q00124A0018002D6Q001A00023Q00122Q001B002E3Q00122Q001C00213Q00202Q001C001C002F4Q001D00096Q001C0002000200122Q001D00306Q001B001B001D4Q001C00016Q001A001C000100044Q00742Q0100060B0112005D2Q013Q0004463Q005D2Q010026210109005D2Q01001F0004463Q005D2Q0100128D000D000F3Q00128D001800313Q0004463Q00742Q01000E02003200642Q0100090004463Q00642Q010006EE001200642Q0100010004463Q00642Q0100128D000D000E3Q00128D001800333Q0004463Q00742Q01002681000900692Q0100170004463Q00692Q0100128D000D000F3Q00128D001800343Q0004463Q00742Q0100060B010F00722Q013Q0004463Q00722Q01002681000900722Q0100160004463Q00722Q010006B4000A00722Q0100170004463Q00722Q0100128D000D000F3Q00128D001800353Q0004463Q00742Q0100128D000D000E3Q00128D001800364Q00AB001A00063Q002014001A001A000C0006EB000D007D2Q01001A0004463Q007D2Q010012FD001A00213Q002014001A001A00252Q00BE001A00010002002681001A00902Q0100370004463Q00902Q0100060B011200822Q013Q0004463Q00822Q0100128D001A00153Q0006EE001A00832Q0100010004463Q00832Q0100128D001A00384Q00AB001B00023Q0012A5001C001C3Q00202Q001C001C001D00122Q001D00396Q001E00063Q00202Q001E001E000C4Q001F000D6Q002000096Q0021000A6Q0022001A6Q002300186Q001C00236Q001B3Q00010026AC000D00DB2Q01000F0004463Q00DB2Q010012FD001A00063Q002039001A001A003B00104Q003A001A00122Q001A00063Q00202Q001A001A003B00104Q003C001A002681000A00A32Q01000D0004463Q00A32Q012Q00AB001A00063Q002014001A001A003D0006EE001A00A02Q0100010004463Q00A02Q012Q00AB001A00063Q001015001A003D00042Q00AB001A00063Q002014000B001A003D0004463Q00A92Q012Q00AB001A00063Q003090001A003D003E4Q000B00066Q001A00053Q00202Q001A001A003F4Q00080008001A2Q00AB001A00063Q002014001A001A000C002625001A00B22Q01000F0004463Q00B22Q01002022001A000400402Q0052001C000B3Q00128D001D00414Q001A001A001D00022Q0052000B001A3Q002014001A000100190006EE001A00B62Q0100010004463Q00B62Q010030052Q010019001A2Q00AB001A00063Q002014001A001A0042000E02000900C02Q01001A0004463Q00C02Q012Q00AB001A00064Q0009011B00063Q00202Q001B001B004200202Q001B001B001700102Q001A0042001B00044Q00E02Q012Q00AB001A00053Q002014001A001A0043002068001A001A000F0006AD000A00C82Q01001A0004463Q00C82Q012Q00AB001A00074Q00BA001A000100010004463Q00E02Q012Q00AB001A00053Q002014001A001A002400060B011A00E02Q013Q0004463Q00E02Q010012FD001A00213Q002014001A001A00252Q00BE001A00010002002681001A00E02Q0100440004463Q00E02Q012Q00AB001A00023Q0012A6001B001C3Q00202Q001B001B001D00122Q001C00456Q001D000A6Q001E00053Q00202Q001E001E00434Q001B001E6Q001A3Q000100044Q00E02Q012Q0052000B00063Q002014001A000100190006EE001A00E02Q0100010004463Q00E02Q010030052Q010019001A2Q0016000C00013Q0006EE000B00E82Q0100010004463Q00E82Q012Q00AB001200023Q00128D001300464Q0016001400014Q002E0012001400012Q00B23Q00014Q00AB001200063Q00201400120012000C0006C500122Q000201000D0004464Q0002012Q0012001200043Q0012B9001300473Q00122Q001400483Q00122Q001500493Q00122Q0016004A6Q0012000400012Q00AB001300023Q0012230014001C3Q00202Q00140014001D00122Q0015004B6Q0016000D6Q00170012000D00062Q001700FB2Q0100010004463Q00FB2Q0100128D0017004C4Q00520018000A3Q002014001900040015002014001A000B00152Q00B10014001A4Q005300133Q00012Q00AB001200063Q0010150012000C000D000E02002300080201000A0004463Q000802012Q00AB001200053Q00201400120012004D2Q00D80008000800120004463Q000D0201002681000A000D020100320004463Q000D02012Q00AB001200053Q00201400120012004E2Q00D800080008001200060B010C001202013Q0004463Q001202012Q00AB001200053Q00201400120012004F2Q00D80008000800122Q00140112000B000400201400120012000B0026810012001A020100260004463Q001A02010012FD001300063Q00201400130013003B0010153Q003A00132Q00B23Q00014Q00140113000B000400201501130013005000122Q001400213Q00202Q0014001400514Q001500086Q001600126Q0014001600024Q0015001300144Q0015000400154Q001600083Q00062Q00160037020100010004463Q003702010012FD001600523Q0020DE00160016000700122Q001700536Q0016000200024Q001600086Q001600083Q00122Q001700063Q00202Q00170017000700122Q001800553Q00122Q001900553Q00122Q001A00556Q0017001A000200102Q0016005400174Q001600083Q00302Q0016005600574Q001600083Q00102Q001600583Q002625000D003A0201000F0004463Q003A02012Q00ED00166Q0016001600013Q00060B0116006C02013Q0004463Q006C02012Q00AB001700083Q00121B011800063Q00202Q00180018003B00102Q0017005400184Q001700083Q00302Q00170056000900202Q0017000200014Q00180017001500202Q00180018000B000E2Q00260062020100180004463Q006202012Q00AB001900063Q00201400190019000C0026AC001900510201000F0004463Q005102010012FD001900213Q0020140019001900252Q00BE00190001000200268100190099020100370004463Q009902010012FD001900593Q0020EA00190019005A4Q001A00156Q001B00176Q0019001B000200202Q001A0019005B4Q001B00023Q00122Q001C001C3Q00202Q001C001C001D00122Q001D005C6Q001E00183Q00202Q001F001A000800202Q0020001A001500202Q0021001A000A4Q001C00216Q001B3Q000100044Q009902012Q00AB001900023Q0012A2001A005D3Q00122Q001B005E6Q001C00186Q001B0002000200122Q001C005F6Q001A001A001C4Q001B00016Q0019001B000100044Q009902010012FD001700063Q00202201170017000700202Q0018000B000800202Q00190015001500202Q001A000B000A4Q0017001A00024Q00180017001500202Q00180018000B000E2Q0026008D020100180004463Q008D02012Q00AB001900053Q0020140019001900600006EE0019007B020100010004463Q007B020100128D001900094Q00AB001A00063Q002014001A001A00610006EE001A0080020100010004463Q008002012Q0052001A00174Q0014011B0017001A002014001B001B000B0006B40019008D0201001B0004463Q008D02012Q00AB001C00083Q0012F5001D00593Q00202Q001D001D005A4Q001E00156Q001F00176Q001D001F000200102Q001C0059001D4Q001C00063Q00102Q001C006100172Q00AB001900083Q0030130019005600574Q001900083Q00302Q0019006200634Q001900083Q00122Q001A00063Q00202Q001A001A000700122Q001B00553Q00122Q001C00553Q00122Q001D00556Q001A001D000200102Q00190054001A0020140017001500080020140018001500080006EB001700F9020100180004463Q00F902010020140017001500150020140018001500150006EB001700F9020100180004463Q00F9020100201400170015000A00201400180015000A0006EB001700F9020100180004463Q00F902010012FD001700213Q0020140017001700220020140018001500082Q000E011700020002002681001700EE020100640004463Q00EE02010012FD001700213Q0020140017001700220020140018001500152Q000E011700020002002681001700EE020100640004463Q00EE02010012FD001700213Q00201400170017002200201400180015000A2Q000E011700020002002681001700EE020100640004463Q00EE02010026AC000D00E80201000F0004463Q00E802012Q00AB001700053Q002014001700170011002625001700BE020100120004463Q00BE02012Q00ED00176Q0016001700013Q0020140018000200012Q001401180018001500201400180018000B000E02002600E2020100180004463Q00E202012Q00AB001900053Q0020140019001900652Q00AB001A00063Q002014001A001A00660006EE001A00CB020100010004463Q00CB0201002014001A00020001002014001B000200012Q0014011B001B001A002014001B001B000B2Q001D011C001C3Q00062F011900D50201001B0004463Q00D502012Q00AB001D00063Q002014001D001D00660006EE001D00DA020100010004463Q00DA02012Q00AB001D00063Q002014001E00020001001015001D0066001E002014001C000200010004463Q00DB02012Q0052001C001A3Q0012FD001D00593Q00200A001D001D005A4Q001E00156Q001F001C6Q001D001F000200104Q0059001D00044Q00FD02010012FD001900593Q0020660019001900074Q001A00156Q00190002000200104Q0059001900044Q00FD02010012FD001700593Q0020660017001700074Q001800156Q00170002000200104Q0059001700044Q00FD02012Q00AB001700023Q00121B0018001C3Q00202Q00180018001D00122Q001900673Q00202Q001A0015000800202Q001B0015001500202Q001C0015000A4Q0018001C00024Q001900016Q00170019000100044Q00FD02012Q00AB001700023Q00128D001800684Q0016001900014Q002E0017001900010012FD001700063Q00201400170017003B0010153Q003A00172Q00B23Q00017Q00143Q00030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F696403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q00506C6174666F726D5374616E64010003043Q004865616403053Q00546F72736F030A3Q00552Q706572546F72736F030A3Q004C6F776572546F72736F03053Q0070616972732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103053Q007072696E7403443Q005B4661726D5D20436C65616E7570506879736963733A20506C6174666F726D5374616E643D66616C73652C2043616E436F2Q6C6964653D7472756520726573746F72656403073Q0044657374726F79003B4Q00AB8Q00BE3Q0001000200060B012Q003200013Q0004463Q003200012Q00AB000100014Q005F00028Q00010002000200202Q00023Q000100122Q000400026Q00020004000200062Q0001001200013Q0004463Q001200010012FD000300043Q00203900030003000500102Q00010003000300122Q000300043Q00202Q00030003000500102Q00010006000300060B0102001800013Q0004463Q0018000100201400030002000700060B0103001800013Q0004463Q001800010030050102000700082Q0012000300043Q0012B9000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q0007000C6Q0003000400010012FD0004000D4Q0052000500035Q000104000200060004463Q002D000100202200093Q00012Q0052000B00084Q001A0009000B000200060B0109002D00013Q0004463Q002D0001002022000A0009000E00128D000C000F4Q001A000A000C000200060B010A002D00013Q0004463Q002D000100300501090010001100067F00040022000100020004463Q002200010012FD000400123Q00128D000500134Q00730004000200012Q00AB000100023Q00060B2Q01003A00013Q0004463Q003A00012Q00AB000100023Q0020220001000100142Q00730001000200012Q001D2Q0100014Q0011000100024Q00B23Q00017Q00043Q0003073Q0044657374726F79030A3Q00446973636F2Q6E65637403053Q007072696E74031C3Q005B4661726D5D2046752Q6C20436C65616E757020436F6D706C65746500224Q0029019Q009Q002Q00018Q000100016Q00028Q000100016Q00033Q00064Q000E00013Q0004463Q000E00012Q00AB3Q00033Q0020225Q00012Q00733Q000200012Q001D017Q00113Q00034Q00AB3Q00043Q00060B012Q001600013Q0004463Q001600012Q00AB3Q00043Q0020225Q00022Q00733Q000200012Q001D017Q00113Q00044Q00AB3Q00053Q00060B012Q001E00013Q0004463Q001E00012Q00AB3Q00053Q0020225Q00022Q00733Q000200012Q001D017Q00113Q00053Q0012FD3Q00033Q00128D000100044Q00733Q000200012Q00B23Q00017Q00283Q0003123Q004D61696E74656E616E6365456E61626C656403103Q0053652Q73696F6E537461727454696D65028Q0003023Q006F7303043Q0074696D65031A3Q004C6173744D61696E74656E616E6365412Q7461636B436F756E7403133Q004C6173744D61696E74656E616E636554696D6503133Q004D61696E74656E616E6365496E74657276616C031A3Q004D61696E74656E616E6365412Q7461636B5468726573686F6C6403043Q006D61746803043Q006875676503103Q004D61696E74656E616E6365436F756E74026Q00F03F03063Q00737472696E6703063Q00666F726D6174030E3Q00253032643A253032643A2530326403053Q00666C2Q6F72025Q0020AC40026Q004E402Q033Q006D6178027B14AE47E17A843F030A3Q00546F74616C4B692Q6C7303103Q00412Q5441434B5F5448524553484F4C4403083Q00494E54455256414C03673Q00204D41494E54454E414E434520232564207C20526561736F6E3A202573207C20557074696D653A202573207C204B692Q6C733A202564207C204B504D3A20252E3266207C2041504D3A20252E3266207C20412Q7461636B732073696E6365206C6173743A202564030E3Q004C6173744C2Q6F6B54617267657400030C3Q004C617374506F736974696F6E030C3Q00537475636B436F756E74657203063Q006763696E666F03163Q00204D6167696343617270657420524546524553484544030B3Q005A6F6E65456E61626C656403073Q0044657374726F7903313Q00205A6F6E65506172742044455354524F594544202877692Q6C207265637265617465206F6E206E657874206672616D652903083Q004175746F4661726D03383Q00204D61696E436F2Q6E656374696F6E20444541442120506C656173652072657374617274204175746F204661726D206D616E75612Q6C792E03053Q007072696E7403373Q005B4661726D5D205741524E494E473A204D61696E436F2Q6E656374696F6E2064696564212052657374617274204175746F204661726D2E03403Q00204D61696E74656E616E636520436F6D706C657465207C20412Q7461636B732072657365743A202564202D3E2030207C204D656D6F72793A20252E3166204B42033D3Q005B4661726D5D204D61696E74656E616E636520232564207C20557074696D653A202573207C204B692Q6C733A202564207C204D656D3A20252E31664B4200B94Q00AB7Q0020145Q00010006EE3Q0005000100010004463Q000500012Q00B23Q00014Q00AB3Q00013Q0020145Q00020026AC3Q000A000100030004463Q000A00012Q00B23Q00013Q0012FD3Q00043Q0020185Q00056Q000100024Q000100026Q000200013Q00202Q00020002000600062Q00020013000100010004463Q0013000100128D000200034Q00142Q01000100022Q00AB000200013Q002014000200020007000E020003001F000100020004463Q001F00012Q00AB000200013Q0020890002000200074Q00023Q00024Q00035Q00202Q00030003000800062Q00030002000100020004463Q002000012Q00ED00026Q0016000200014Q00AB00035Q0020140003000300090006EE00030027000100010004463Q002700010012FD0003000A3Q00201400030003000B00060500030002000100010004463Q002A00012Q00ED00036Q0016000300013Q0006EE00020030000100010004463Q003000010006EE00030030000100010004463Q003000012Q00B23Q00014Q00AB000400013Q0010D2000400076Q000400016Q000500013Q00202Q00050005000C00202Q00050005000D00102Q0004000C00054Q000400016Q000500023Q00102Q0004000600054Q000400013Q00202Q0004000400024Q00043Q000400122Q0005000E3Q00202Q00050005000F00122Q000600103Q00122Q0007000A3Q00202Q00070007001100202Q0008000400124Q00070002000200122Q0008000A3Q00202Q00080008001100202Q00090004001200202Q0009000900134Q00080002000200202Q0009000400134Q00050009000200122Q0006000A3Q00202Q00060006001400202Q00070004001300122Q000800156Q0006000800024Q000700013Q00202Q0007000700164Q0007000700064Q000800026Q00080008000600062Q0003005A00013Q0004463Q005A000100128D000900173Q0006EE0009005B000100010004463Q005B000100128D000900184Q00AB000A00033Q0012CA000B000E3Q00202Q000B000B000F00122Q000C00196Q000D00013Q00202Q000D000D000C4Q000E00096Q000F00056Q001000013Q00202Q0010001000164Q001100076Q001200086Q001300016Q000B00136Q000A3Q00014Q000A00023Q00122Q000B00036Q000B00026Q000B00013Q00302Q000B000600034Q000B00013Q00302Q000B001A001B4Q000B00013Q00302Q000B001C001B4Q000B00013Q00302Q000B001D000300122Q000B001E3Q00062Q000B007C00013Q0004463Q007C00010012FD000B001E4Q00BE000B000100020006EE000B007D000100010004463Q007D000100128D000B00034Q00AB000C00043Q00060B010C008700013Q0004463Q008700012Q00AB000C00054Q0018010C000100014Q000C00066Q000C000100014Q000C00033Q00122Q000D001F6Q000C000200012Q00AB000C5Q002014000C000C002000060B010C009600013Q0004463Q009600012Q00AB000C00073Q00060B010C009600013Q0004463Q009600012Q00AB000C00073Q002097000C000C00214Q000C000200014Q000C000C6Q000C00076Q000C00033Q00122Q000D00226Q000C000200012Q00AB000C5Q002014000C000C002300060B010C00A400013Q0004463Q00A400012Q00AB000C00083Q0006EE000C00A4000100010004463Q00A400012Q00AB000C00033Q001207000D00246Q000E00016Q000C000E000100122Q000C00253Q00122Q000D00266Q000C000200012Q00AB000C00033Q001264000D000E3Q00202Q000D000D000F00122Q000E00276Q000F000A6Q0010000B6Q000D00106Q000C3Q000100122Q000C00253Q00122Q000D000E3Q00202Q000D000D000F00122Q000E00286Q000F00013Q00202Q000F000F000C4Q001000056Q001100013Q00202Q0011001100164Q0012000B6Q000D00126Q000C3Q00016Q00017Q000C3Q0003053Q007063612Q6C03053Q005469746C65030C3Q00204D61696E74656E616E636503073Q00436F6E74656E7403113Q00436C65616E757020636F6D706C6574652103083Q004475726174696F6E027Q004003043Q007761726E03223Q005B466F726765204661726D5D20466F72636520436C65616E757020452Q524F523A2003083Q00746F737472696E6703063Q0020452Q726F72026Q001440001F3Q0012FD3Q00013Q0006102Q013Q000100022Q00AB8Q00AB3Q00015Q00012Q0002000100060B012Q000E00013Q0004463Q000E00012Q00AB000200024Q007D00033Q000300302Q00030002000300302Q00030004000500302Q0003000600074Q00020002000100044Q001E00010012FD000200083Q001227010300093Q00122Q0004000A6Q000500016Q0004000200024Q0003000300044Q0002000200014Q000200026Q00033Q000300302Q00030002000B00122Q0004000A6Q000500016Q00040002000200102Q00030004000400302Q00030006000C4Q0002000200012Q00B23Q00013Q00013Q00053Q0003103Q0053652Q73696F6E537461727454696D65028Q0003023Q006F7303043Q0074696D6503133Q004C6173744D61696E74656E616E636554696D65000E4Q00AB7Q0020145Q00010026AC3Q0009000100020004463Q000900012Q00AB7Q0012FD000100033Q0020140001000100042Q00BE0001000100020010153Q000100012Q00AB7Q003005012Q000500022Q00AB3Q00014Q00BA3Q000100012Q00B23Q00017Q001B3Q0003103Q0053652Q73696F6E537461727454696D6503023Q006F7303043Q0074696D6503133Q004C6173744D61696E74656E616E636554696D65030A3Q00546F74616C4B692Q6C73028Q0003103Q004D61696E74656E616E6365436F756E74031A3Q004C6173744D61696E74656E616E6365412Q7461636B436F756E7403123Q00204175746F204661726D205354415254454403063Q00737472696E6703063Q00666F726D617403373Q002053652Q74696E67733A204865696768743D252E31662C2053702Q65643D25642C2052616E67653D25642C2044697374616E63653D256403063Q00486569676874030A3Q0047686F737453702Q656403093Q004661726D52616E676503083Q0044697374616E6365031A3Q002053656C65637465644D6F62733A2025642073656C6563746564030C3Q0053656C65637465644D6F627303063Q0069706169727303053Q003Q202D2003083Q00746F737472696E6703093Q0048656172746265617403073Q00436F2Q6E65637403043Q007461736B03053Q00737061776E03053Q007072696E7403133Q005B4661726D5D204C2Q6F70205374617274656400734Q00AB7Q00060B012Q000400013Q0004463Q000400012Q00B23Q00014Q00AB3Q00013Q00129F000100023Q00202Q0001000100034Q00010001000200104Q000100016Q00013Q00122Q000100023Q00202Q0001000100034Q00010001000200104Q000400016Q00013Q00304Q000500066Q00013Q00304Q000700066Q00016Q000100023Q00104Q000800016Q00013Q00122Q000100023Q00202Q0001000100034Q00010001000200104Q000400016Q00033Q00122Q000100098Q000200016Q00033Q00122Q0001000A3Q00202Q00010001000B00122Q0002000C6Q000300043Q00202Q00030003000D4Q000400043Q00202Q00040004000E4Q000500043Q00202Q00050005000F4Q000600043Q00202Q0006000600104Q000100069Q0000016Q00033Q00122Q0001000A3Q00202Q00010001000B00122Q000200116Q000300043Q00202Q0003000300124Q000300036Q000100039Q00000100124Q00136Q000100043Q00202Q0001000100126Q0002000200044Q004000012Q00AB000500033Q001237000600143Q00122Q000700156Q000800046Q0007000200024Q0006000600074Q00050002000100067F3Q0039000100020004463Q003900012Q00AB3Q00054Q00BA3Q000100012Q00AB3Q00073Q0020145Q00160020225Q001700061001023Q000100052Q00AB3Q00044Q00AB3Q00084Q00AB3Q00094Q00AB3Q000A4Q00AB3Q000B4Q00043Q000200026Q00068Q00073Q00206Q001600206Q0017000610010200010001000E2Q00AB3Q00044Q00AB3Q000C4Q00AB3Q00084Q00AB3Q000D4Q00AB3Q00014Q00AB3Q000E4Q00AB3Q00034Q00AB3Q000F4Q00AB3Q00104Q00AB3Q00024Q00AB3Q00114Q00AB3Q00124Q00AB3Q00054Q00AB3Q00134Q00823Q000200029Q006Q00148Q000100016Q00018Q00153Q00124Q00183Q00206Q00190006102Q010002000100042Q00AB3Q00154Q00AB3Q00044Q00AB8Q00AB3Q00034Q00363Q0002000100124Q001A3Q00122Q0001001B8Q000200016Q00013Q00033Q000C3Q0003083Q004175746F4661726D030A3Q00446973636F2Q6E65637403053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q0042617365506172742Q01030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637403063Q00506172656E74030A3Q0043616E436F2Q6C696465012Q003A4Q00AB7Q0020145Q00010006EE3Q0005000100010004463Q000500012Q00B23Q00014Q00AB3Q00014Q00BE3Q000100020006EE3Q000A000100010004463Q000A00012Q00B23Q00014Q00AB000100023Q0006C53Q002C000100010004463Q002C00012Q001200016Q0011000100034Q00113Q00024Q00AB000100043Q00060B2Q01001800013Q0004463Q001800012Q00AB000100043Q0020220001000100022Q00730001000200012Q001D2Q0100014Q0011000100043Q0012FD000100033Q00202200023Q00042Q0078000200034Q001E2Q013Q00030004463Q0024000100202200060005000500128D000800064Q001A00060008000200060B0106002400013Q0004463Q002400012Q00AB000600033Q00207500060005000700067F0001001D000100020004463Q001D000100201400013Q000800202200010001000900061001033Q000100012Q00AB3Q00034Q001A0001000300022Q0011000100043Q0012FD000100034Q00AB000200035Q002Q01000200030004463Q0037000100201400050004000A00060B0105003700013Q0004463Q0037000100201400050004000B00060B0105003700013Q0004463Q003700010030050104000B000C00067F00010030000100010004463Q003000012Q00B23Q00013Q00013Q00053Q002Q033Q0049734103083Q0042617365506172742Q01030A3Q0043616E436F2Q6C696465010001093Q00202200013Q000100128D000300024Q001A00010003000200060B2Q01000800013Q0004463Q000800012Q00AB00015Q00207500013Q0003003005012Q000400052Q00B23Q00017Q00073Q0003053Q007063612Q6C03043Q007761726E03183Q005B4661726D5D2048656172746265617420652Q726F723A2003083Q00746F737472696E6703083Q004175746F4661726D0100030C3Q0053746F704661726D4C2Q6F7001203Q0012FD000100013Q00061001023Q0001000F2Q00AB8Q00AB3Q00014Q00AB3Q00024Q00AB3Q00034Q00AB3Q00044Q00AB3Q00054Q00AB3Q00064Q00AB3Q00074Q00AB3Q00084Q00AB3Q00094Q00AB3Q000A4Q00AB3Q000B4Q00AB3Q000C4Q00528Q00AB3Q000D5Q002Q01000200020006EE0001001F000100010004463Q001F00010012FD000300023Q001237000400033Q00122Q000500046Q000600026Q0005000200024Q0004000400054Q0003000200012Q00AB00035Q0030050103000500060012FD000300074Q00BA0003000100012Q00B23Q00013Q00013Q003E3Q0003083Q004175746F4661726D030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030C3Q0043752Q72656E745068617365028Q00030D3Q0043752Q72656E7454617267657400030A3Q00536B69704672616D6573026Q000840032D3Q002043686172616374657220646965642F7265737061776E696E67202D20506861736520726573657420746F2030030D3Q004C6173744E6F436861724C6F6703043Q007469636B026Q00F03F03063Q00737472696E6703063Q00666F726D617403273Q00204E4F20434841522F522Q4F543A20636861723D25732C20722Q6F743D25732C2068756D3D257303083Q00746F737472696E67030F3Q005072696F72697479456E61626C656403113Q004C6173745072696F72697479436865636B029A5Q99C93F03043Q004E616D65030D3Q004D6F625072696F72697469657303223Q00205052494F52495459205357495443483A20257328502564292Q202573285025642903103Q00536B6970412Q7461636B4672616D6573026Q001440030F3Q004C6F636B6564412Q7461636B506F73030F3Q0042656C6F7744657363656E64696E67010003103Q004C617374546172676574536561726368030F3Q004C6173744E6F5461726765744C6F67027Q004003343Q00204E4F2054415247455420464F554E44207C2053656C65637465644D6F62733A202564207C20466C696768744D6F64653A202573030C3Q0053656C65637465644D6F6273030A3Q00466C696768744D6F6465030E3Q0020546172676574204C6F73743A20030A3Q00546F74616C4B692Q6C7303083Q00506F736974696F6E03093Q004D61676E6974756465031C3Q00204E6577205461726765743A2025732028252E316620737475647329030B3Q002053776974636865643A2003023Q002Q20026Q002E40030E3Q004C6173744C2Q6F6B546172676574030E3Q005361666548656967687449646C6503013Q0059030B3Q004C61737449646C654C6F6703093Q00415343454E44494E4703083Q00484F564552494E47031E3Q002049444C45207C20593A252E31662Q20536166653A252E3166207C202573030A3Q0047686F737453702Q656403073Q00566563746F72332Q033Q006E657703013Q005803013Q005A03043Q00556E697403163Q00412Q73656D626C794C696E65617256656C6F6369747903043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F6369747903063Q00434672616D65030D3Q00506C6174666F726D5374616E642Q01032D3Q002054617267657420722Q6F7420626563616D65206E696C20286D6F622064696564206D69642D666C696768742900D2013Q00AB7Q0020145Q00010006EE3Q0005000100010004463Q000500012Q00B23Q00014Q00AB3Q00014Q00863Q000100016Q00028Q000100024Q000100036Q00028Q00010002000200062Q0002001100013Q0004463Q0011000100202200023Q000200128D000400034Q001A00020004000200060B2Q01001500013Q0004463Q001500010006EE0002004D000100010004463Q004D00012Q00AB000300043Q00201400030003000400262500030024000100050004463Q002400012Q00AB000300043Q0030450003000400054Q000300043Q00302Q0003000600074Q000300043Q00302Q0003000800094Q000300056Q0003000100014Q000300063Q00122Q0004000A6Q0003000200012Q00AB000300043Q00201400030003000B00060B0103002F00013Q0004463Q002F00010012FD0003000C4Q00940003000100024Q000400043Q00202Q00040004000B4Q000300030004000E2Q000D004C000100030004463Q004C00012Q00AB000300063Q00125E0004000E3Q00202Q00040004000F00122Q000500103Q00122Q000600113Q00264Q0037000100070004463Q003700012Q00ED00076Q0016000700014Q000E0106000200020012FD000700113Q0026AC0001003D000100070004463Q003D00012Q00ED00086Q0016000800014Q000E0107000200020012FD000800113Q0026AC00020043000100070004463Q004300012Q00ED00096Q0016000900014Q00B5000800096Q00043Q00024Q000500016Q0003000500014Q000300043Q00122Q0004000C6Q00040001000200102Q0003000B00042Q00B23Q00013Q0012FD0003000C4Q00BE0003000100022Q00AB000400043Q00201400040004000600060B0104009100013Q0004463Q009100012Q00AB00045Q00201400040004001200060B0104009100013Q0004463Q009100012Q00AB000400043Q0020140004000400132Q0014010400030004000E2B00140091000100040004463Q009100012Q00AB000400043Q0010310004001300034Q000400076Q000500043Q00202Q0005000500064Q00040002000200062Q0004009100013Q0004463Q009100012Q00AB000500084Q009C000600043Q00202Q00060006000600202Q0006000600154Q0005000200024Q00065Q00202Q0006000600164Q00060006000500062Q0006006F000100010004463Q006F000100128D000600054Q00AB000700083Q00208A0008000400154Q0007000200024Q00085Q00202Q0008000800164Q00080008000700062Q00080078000100010004463Q0078000100128D000800054Q00AB000900063Q0012D5000A000E3Q00202Q000A000A000F00122Q000B00176Q000C00056Q000D00066Q000E00076Q000F00086Q000A000F00024Q000B00016Q0009000B00014Q000900043Q00102Q0009000600044Q000900043Q00302Q0009000400054Q000900043Q00302Q0009000800094Q000900043Q00302Q0009001800194Q000900043Q00302Q0009001A00074Q000900043Q00302Q0009001B001C00122Q000900056Q000900094Q00AB000400043Q00201400040004000600060B0104009B00013Q0004463Q009B00012Q00AB0004000A4Q00AB000500043Q0020140005000500062Q000E0104000200020006EE0004004F2Q0100010004463Q004F2Q012Q00AB000400043Q0020140004000400060006EE000400AB000100010004463Q00AB00012Q00AB000400043Q00201400040004001D00060B010400AB00013Q0004463Q00AB00010012FD0004000C4Q009A0004000100024Q000500043Q00202Q00050005001D4Q00040004000500262Q000400AB000100140004463Q00AB00010004463Q004F2Q012Q00AB000400043Q0012800005000C6Q00050001000200102Q0004001D00054Q000400043Q00202Q0004000400064Q000500046Q0006000B6Q00060001000200102Q0005000600064Q000500043Q00202Q00050005000600062Q000500D4000100010004463Q00D400012Q00AB000500043Q00201400050005001E00060B010500C400013Q0004463Q00C400010012FD0005000C4Q00940005000100024Q000600043Q00202Q00060006001E4Q000500050006000E2Q001F00D4000100050004463Q00D400012Q00AB000500063Q0012960006000E3Q00202Q00060006000F00122Q000700206Q00085Q00202Q0008000800214Q000800086Q00095Q00202Q0009000900224Q0006000900024Q000700016Q0005000700014Q000500043Q00122Q0006000C6Q00060001000200102Q0005001E000600060B010400F300013Q0004463Q00F300012Q00AB000500043Q0020140005000500060006EE000500F3000100010004463Q00F300012Q00AB000500063Q001263000600236Q000700083Q00202Q0008000400154Q0007000200024Q0006000600074Q0005000200014Q0005000C6Q0005000100014Q000500046Q000600043Q00202Q00060006002400202Q00060006000D00102Q0005002400064Q000500043Q00302Q0005000400054Q000500043Q00302Q0005000800094Q000500043Q00302Q0005001800194Q000500043Q00302Q0005001B001C4Q000500043Q00302Q0005001A000700044Q004F2Q010006EE000400202Q0100010004463Q00202Q012Q00AB000500043Q00201400050005000600060B010500202Q013Q0004463Q00202Q012Q00AB000500034Q00AB000600043Q0020140006000600062Q000E01050002000200060B010500052Q013Q0004463Q00052Q010020140006000500250020140007000100252Q00140106000600070020140006000600260006EE000600062Q0100010004463Q00062Q0100128D000600054Q00AB000700063Q0012060108000E3Q00202Q00080008000F00122Q000900276Q000A00086Q000B00043Q00202Q000B000B000600202Q000B000B00154Q000A000200024Q000B00066Q0008000B6Q00073Q00014Q0007000C6Q00070001000100122Q000700056Q000700096Q000700043Q00302Q0007000400054Q000700043Q00302Q0007000800094Q000700043Q00302Q0007001800194Q000700043Q00302Q0007001B001C6Q00013Q00044Q004F2Q0100060B0104004F2Q013Q0004463Q004F2Q012Q00AB000500043Q00201400050005000600060B0105004F2Q013Q0004463Q004F2Q012Q00AB000500043Q0020140005000500060006C50004004F2Q0100050004463Q004F2Q012Q00AB000500063Q001201000600286Q000700083Q00202Q0008000400154Q00070002000200122Q000800296Q000900086Q000A00043Q00202Q000A000A000600202Q000A000A00154Q0009000200024Q0006000600094Q0005000200014Q0005000C6Q00050001000100122Q000500056Q000500096Q000500043Q00302Q0005000400054Q000500043Q00302Q0005000800094Q000500043Q00302Q00050018002A4Q000500043Q00302Q0005001B001C4Q000500043Q00302Q0005001A00074Q000500036Q000600043Q00202Q0006000600064Q00050002000200062Q0005004E2Q013Q0004463Q004E2Q012Q00AB000600043Q0020140007000500250010150006002B00072Q00B23Q00014Q00AB000400043Q0020140004000400060006EE000400A82Q0100010004463Q00A82Q012Q00AB00045Q00203000040004002C00202Q00050001002500202Q00050005002D4Q000600043Q00202Q00060006002E00062Q000600622Q013Q0004463Q00622Q010012FD0006000C4Q00940006000100024Q000700043Q00202Q00070007002E4Q000600060007000E2Q001F00762Q0100060004463Q00762Q010020A10006000400190006B4000500682Q0100060004463Q00682Q0100128D0006002F3Q0006EE000600692Q0100010004463Q00692Q0100128D000600304Q00AB000700063Q00120F0008000E3Q00202Q00080008000F00122Q000900316Q000A00056Q000B00046Q000C00066Q0008000C6Q00073Q00014Q000700043Q00122Q0008000C6Q00080001000200102Q0007002E00080020A10006000400190006B40005009B2Q0100060004463Q009B2Q012Q00AB00065Q0020090006000600324Q0007000D6Q00060006000700122Q000700333Q00202Q00070007003400202Q00080001002500202Q0008000800354Q000900043Q00202Q000A0001002500202Q000A000A00364Q0007000A000200202Q0008000100254Q00080007000800202Q00080008003700202Q0009000100254Q000A000800064Q00090009000A00122Q000A00333Q00202Q000A000A003900102Q00010038000A00122Q000A00333Q00202Q000A000A003900102Q0001003A000A00122Q000A003B3Q00202Q000A000A00344Q000B00096Q000A0002000200102Q0001003B000A00202Q000A0002003C00062Q000A00A52Q0100010004463Q00A52Q010030050102003C003D0004463Q00A52Q010012FD000600333Q00203900060006003900102Q00010038000600122Q000600333Q00202Q00060006003900102Q0001003A000600201400060002003C0006EE000600A52Q0100010004463Q00A52Q010030050102003C003D2Q00AB000600043Q0030050106000400052Q00B23Q00014Q00AB000400043Q002014000400040008000E02000500BC2Q0100040004463Q00BC2Q012Q00AB000400044Q00CE000500043Q00202Q00050005000800202Q00050005000D00102Q00040008000500122Q000400333Q00202Q00040004003900102Q00010038000400122Q000400333Q00202Q00040004003900102Q0001003A000400202Q00040002003C00062Q000400BB2Q0100010004463Q00BB2Q010030050102003C003D2Q00B23Q00014Q00AB000400034Q00AB000500043Q0020140005000500062Q000E0104000200020006EE000400CB2Q0100010004463Q00CB2Q012Q00AB000500063Q0012C10006003E6Q000700016Q0005000700014Q000500056Q0005000100014Q000500043Q00302Q0005000600076Q00014Q00AB0005000E4Q003E000600016Q000700026Q000800046Q0009000D6Q0005000900016Q00017Q00073Q0003043Q007461736B03043Q0077616974026Q00144003083Q004175746F4661726D03343Q005761746368646F673A204D61696E436F2Q6E656374696F6E206D692Q73696E672C2073746F2Q70696E67204175746F204661726D0100030C3Q0053746F704661726D4C2Q6F70001A4Q00AB7Q00060B012Q001900013Q0004463Q001900010012FD3Q00013Q00201A014Q000200122Q000100038Q000200016Q00013Q00206Q000400064Q000C000100010004463Q000C00010004463Q001900012Q00AB3Q00023Q0006EE5Q000100010004465Q00012Q00AB3Q00033Q00128F000100056Q000200018Q000200016Q00013Q00304Q0004000600124Q00078Q0001000100044Q001900010004465Q00012Q00B23Q00017Q00083Q00030A3Q00446973636F2Q6E65637403073Q0044657374726F79030D3Q0043752Q72656E7454617267657400028Q0003123Q00204175746F204661726D2053544F2Q50454403053Q007072696E7403263Q005B4661726D5D204C2Q6F702053746F2Q706564202D20436C65616E757020436F6D706C657465002B4Q00AB7Q00060B012Q000800013Q0004463Q000800012Q00AB7Q0020225Q00012Q00733Q000200012Q001D017Q00118Q00AB3Q00013Q00060B012Q001000013Q0004463Q001000012Q00AB3Q00013Q0020225Q00012Q00733Q000200012Q001D017Q00113Q00014Q00168Q00E23Q00028Q00038Q000100016Q00048Q000100016Q00053Q00064Q001E00013Q0004463Q001E00012Q00AB3Q00053Q0020225Q00022Q00733Q000200012Q001D017Q00113Q00054Q00AB3Q00063Q0030723Q0003000400124Q00058Q00078Q00088Q000100016Q00093Q00122Q000100068Q0002000100124Q00073Q00122Q000100088Q000200016Q00017Q00233Q00030B3Q005A6F6E65456E61626C656403083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503083Q004661726D5A6F6E6503083Q004D6174657269616C03043Q00456E756D030A3Q00466F7263654669656C6403053Q00436F6C6F7203063Q00436F6C6F7233028Q00026Q00F03F030C3Q005472616E73706172656E6379026Q00E03F030A3Q0043616E436F2Q6C696465010003083Q00416E63686F7265642Q0103063Q00506172656E74030A3Q005A6F6E6543656E74657203043Q0053697A6503073Q00566563746F723303083Q005A6F6E654C65667403093Q005A6F6E65526967687403063Q005A6F6E65557003083Q005A6F6E65446F776E03093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B027Q004003083Q00506F736974696F6E03013Q005803013Q005903013Q005A03073Q0044657374726F7900614Q00AB7Q0020145Q000100060B012Q005800013Q0004463Q005800012Q00AB3Q00013Q0006EE3Q0024000100010004463Q002400010012FD3Q00023Q00205C5Q000300122Q000100048Q000200026Q00018Q00013Q00304Q000500066Q00013Q00122Q000100083Q00202Q00010001000700202Q00010001000900104Q000700016Q00013Q00122Q0001000B3Q00202Q00010001000300122Q0002000C3Q00122Q0003000D3Q00122Q0004000C6Q00010004000200104Q000A00016Q00013Q00304Q000E000F6Q00013Q00304Q001000116Q00013Q00304Q001200136Q00016Q000100023Q00104Q001400012Q00AB7Q00205A5Q00154Q000100013Q00122Q000200173Q00202Q0002000200034Q00035Q00202Q0003000300184Q00045Q00202Q0004000400194Q0003000300044Q00045Q00202Q00040004001A4Q00055Q00202Q00050005001B4Q0004000400054Q00055Q00202Q00050005001C4Q00065Q00202Q00060006001D4Q0005000500064Q00020005000200102Q0001001600024Q00015Q00202Q0001000100194Q00025Q00202Q0002000200184Q00010001000200202Q00010001001E4Q00025Q00202Q00020002001A4Q00035Q00202Q00030003001B4Q00020002000300202Q00020002001E4Q00035Q00202Q00030003001D4Q00045Q00202Q00040004001C4Q00030003000400202Q00030003001E4Q000400013Q00122Q000500173Q00202Q00050005000300202Q00063Q00204Q00060006000100202Q00073Q00214Q00070007000200202Q00083Q00224Q0008000800034Q00050008000200102Q0004001F000500044Q006000012Q00AB3Q00013Q00060B012Q006000013Q0004463Q006000012Q00AB3Q00013Q0020225Q00232Q00733Q000200012Q001D017Q00113Q00014Q00B23Q00017Q000F3Q0003023Q005F4703053Q00466F726765030C3Q004D696E696E67436F6E666967030A3Q004175746F4D696E696E67030A3Q0053746F704D696E696E67010003103Q004D696E696E675549456C656D656E747303103Q004175746F4D696E696E67546F2Q676C6503053Q007063612Q6C03053Q005469746C6503093Q004175746F204661726D03073Q00436F6E74656E7403273Q004175746F204D696E696E672064697361626C656420746F2061766F696420636F6E666C6963747303083Q004475726174696F6E027Q004000253Q0012FD3Q00013Q0020145Q00020006DC0001000500013Q0004463Q0005000100201400013Q000300060B2Q01002400013Q0004463Q0024000100201400020001000400060B0102002400013Q0004463Q0024000100201400023Q000500060B0102001000013Q0004463Q0010000100201400023Q00052Q00BA0002000100010004463Q001E00010030052Q01000400060006DC0002001400013Q0004463Q0014000100201400023Q000700060B0102001D00013Q0004463Q001D000100201400030002000800060B0103001D00013Q0004463Q001D00010012FD000300093Q00061001043Q000100012Q00523Q00024Q00730003000200012Q008E00026Q00AB00026Q003101033Q000300302Q0003000A000B00302Q0003000C000D00302Q0003000E000F4Q0002000200012Q00B23Q00013Q00013Q00023Q0003103Q004175746F4D696E696E67546F2Q676C652Q033Q0053657400064Q00C37Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00013Q0003083Q004175746F4661726D010E3Q00060B012Q000400013Q0004463Q000400012Q00AB00016Q00BA0001000100012Q00AB000100013Q001015000100013Q00060B012Q000B00013Q0004463Q000B00012Q00AB000100024Q00BA0001000100010004463Q000D00012Q00AB000100034Q00BA0001000100012Q00B23Q00017Q00023Q00030E3Q00537475636B446574656374696F6E03073Q00456E61626C656401044Q00AB00015Q002014000100010001001015000100024Q00B23Q00019Q003Q00034Q00AB8Q00BA3Q000100012Q00B23Q00017Q00143Q0003023Q006F7303043Q0074696D6503103Q0053652Q73696F6E537461727454696D6503063Q00737472696E6703063Q00666F726D6174030E3Q00253032643A253032643A2530326403043Q006D61746803053Q00666C2Q6F72025Q0020AC40026Q004E4003063Q006763696E666F028Q0003053Q005469746C65030E3Q002053652Q73696F6E20537461747303073Q00436F6E74656E7403313Q00557074696D653A2025730A4B692Q6C733A2025640A436C65616E7570733A2025640A4D656D6F72793A20252E3166204B42030A3Q00546F74616C4B692Q6C7303103Q004D61696E74656E616E6365436F756E7403083Q004475726174696F6E026Q001440002D3Q001211012Q00013Q00206Q00026Q000100024Q00015Q00202Q0001000100038Q000100122Q000100043Q00202Q00010001000500122Q000200063Q00122Q000300073Q00202Q00030003000800202Q00043Q00094Q00030002000200122Q000400073Q00202Q00040004000800202Q00053Q000900202Q00050005000A4Q00040002000200202Q00053Q000A4Q00010005000200122Q0002000B3Q00062Q0002001B00013Q0004463Q001B00010012FD0002000B4Q00BE0002000100020006EE0002001C000100010004463Q001C000100128D0002000C4Q00AB000300014Q001901043Q000300302Q0004000D000E00122Q000500043Q00202Q00050005000500122Q000600106Q000700016Q00085Q00202Q0008000800114Q00095Q00202Q0009000900124Q000A00026Q0005000A000200102Q0004000F000500302Q0004001300144Q0003000200016Q00017Q001C3Q00030C3Q0053656C65637465644D6F6273030D3Q0043752Q72656E7454617267657400030A3Q00536B69704672616D6573026Q001440030C3Q0043752Q72656E745068617365028Q00030D3Q004D6F625072696F72697469657303063Q00697061697273026Q00F03F03083Q004D6F624C6162656C03053Q007461626C6503063Q00636F6E63617403023Q002C20030A3Q0028612Q6C206D6F62732903053Q007063612Q6C030D3Q005072696F726974794C6162656C2Q033Q003173742Q033Q00326E642Q033Q003372642Q033Q003474682Q033Q003574682Q033Q003674682Q033Q003774682Q033Q0038746803063Q00696E7365727403023Q00746803023Q003A20015B4Q004800015Q00102Q000100016Q000100013Q00302Q0001000200034Q000100013Q00302Q0001000400054Q000100013Q00302Q0001000600074Q00018Q00025Q00102Q0001000800024Q00015Q00122Q000200096Q00038Q00020002000400044Q001500012Q00AB00075Q0020140007000700082Q001401080001000500206800080008000A2Q00C000070006000800067F00020010000100020004463Q001000012Q00AB000200023Q00201400020002000B00060B0102002B00013Q0004463Q002B0001000E0200070024000100010004463Q002400010012FD0002000C3Q00207A00020002000D4Q00035Q00122Q0004000E6Q00020004000200062Q00020025000100010004463Q0025000100128D0002000F3Q0012FD000300103Q00061001043Q000100022Q00AB3Q00024Q00523Q00024Q00730003000200012Q008E00026Q00AB000200023Q00201400020002001100060B0102005A00013Q0004463Q005A0001000E02000A0056000100010004463Q005600012Q0012000200083Q0012BC000300123Q00122Q000400133Q00122Q000500143Q00122Q000600153Q00122Q000700163Q00122Q000800173Q00122Q000900183Q00122Q000A00196Q0002000800012Q001200035Q0012FD000400094Q005200057Q000104000200060004463Q004D00010012FD0009000C3Q00201400090009001A2Q0052000A00034Q003F000B000200070006EE000B0049000100010004463Q004900012Q0052000B00073Q00128D000C001B4Q00D4000B000B000C00128D000C001C4Q0052000D00084Q00D4000B000B000D2Q002E0009000B000100067F00040040000100020004463Q004000010012FD000400103Q00061001050001000100022Q00AB3Q00024Q00523Q00034Q00730004000200012Q008E00025Q0004463Q005A00010012FD000200103Q00061001030002000100012Q00AB3Q00024Q00730002000200012Q00B23Q00013Q00033Q00033Q0003083Q004D6F624C6162656C2Q033Q0053657403013Q002000084Q00A77Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q00063Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403013Q002003053Q007461626C6503063Q00636F6E63617403023Q002Q20000C4Q00EC7Q00206Q000100206Q000200122Q000200033Q00122Q000300043Q00202Q0003000300054Q000400013Q00122Q000500066Q0003000500024Q0002000200036Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q00536574031C3Q002053656C65637420322B206D6F627320666F72207072696F7269747900064Q002Q016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00073Q0003093Q00426C61636B6C697374030D3Q0043752Q72656E7454617267657400030A3Q00536B69704672616D6573026Q000840030C3Q0043752Q72656E745068617365028Q0001094Q00A800015Q00102Q000100016Q000100013Q00302Q0001000200034Q000100013Q00302Q0001000400054Q000100013Q00302Q0001000600076Q00017Q00013Q0003123Q0049676E6F7265496E76756C6E657261626C6501034Q00AB00015Q001015000100014Q00B23Q00017Q000E3Q0003043Q007469636B030F3Q004C6173745265667265736854696D65026Q00F03F03053Q005469746C6503043Q005761697403073Q00436F6E74656E74032C3Q00506C6561736520776169742061206D6F6D656E74206265666F72652072656672657368696E6720616761696E03083Q004475726174696F6E027Q0040028Q0003053Q007063612Q6C03093Q0052656672657368656403063Q00466F756E642003053Q00206D6F627300313Q0012873Q00018Q000100024Q00015Q00202Q00010001000200062Q0001001200013Q0004463Q001200012Q00AB00015Q0020140001000100022Q00142Q013Q000100268100010012000100030004463Q001200012Q00AB000100014Q00DF00023Q000300302Q00020004000500302Q00020006000700302Q0002000800094Q0001000200016Q00014Q00AB00015Q0010B7000100026Q000100036Q0001000100024Q000100026Q000100026Q000100013Q000E2Q000A0030000100010004463Q003000010012FD0001000B3Q00061001023Q000100022Q00AB3Q00044Q00AB3Q00024Q00730001000200010012FD0001000B3Q00061001020001000100022Q00AB3Q00044Q00AB3Q00024Q002C2Q01000200014Q000100016Q00023Q000300302Q00020004000C00122Q0003000D6Q000400026Q000400043Q00122Q0005000E6Q00030003000500102Q00020006000300302Q0002000800094Q0001000200012Q00B23Q00013Q00023Q00023Q00030B3Q004D6F6244726F70646F776E03073Q005265667265736800064Q002A016Q00206Q000100206Q00024Q000200018Q000200016Q00017Q00023Q0003113Q00426C61636B6C69737444726F70646F776E03073Q0052656672657368000A4Q00AB7Q0020145Q000100060B012Q000900013Q0004463Q000900012Q00AB7Q0020145Q00010020225Q00022Q00AB000200014Q002E3Q000200012Q00B23Q00017Q00013Q00030F3Q005072696F72697479456E61626C656401034Q00AB00015Q001015000100014Q00B23Q00017Q001C3Q00030C3Q0053656C65637465644D6F6273027Q004003053Q005469746C6503083Q005072696F7269747903073Q00436F6E74656E7403153Q0053656C65637420322B206D6F62732066697273742103083Q004475726174696F6E03063Q00697061697273030D3Q004D6F625072696F726974696573026Q00F03F03053Q007461626C6503063Q00696E736572742Q033Q006D6F6203013Q007003043Q00736F72742Q033Q003173742Q033Q00326E642Q033Q003372642Q033Q003474682Q033Q003574682Q033Q003674682Q033Q003774682Q033Q0038746803023Q00746803023Q003A20030D3Q005072696F726974794C6162656C03053Q007063612Q6C030F3Q004F726465722072657665727365642100644Q00AB7Q0020145Q00012Q004900015Q0026810001000C000100020004463Q000C00012Q00AB000100014Q00DF00023Q000300302Q00020003000400302Q00020005000600302Q0002000700024Q0001000200016Q00014Q001200016Q00CC00025Q00122Q000300086Q00048Q00030002000500044Q001C00012Q00AB00085Q0020140008000800092Q003F0008000800070006EE00080019000100010004463Q001900012Q001401080002000600206800080008000A2Q001401090002000800206800090009000A2Q00C000010007000900067F00030012000100020004463Q001200012Q00AB00035Q0010C90003000900014Q00035Q00122Q000400086Q00058Q00040002000600044Q002F00010012FD0009000B3Q00202800090009000C4Q000A00036Q000B3Q000200102Q000B000D00084Q000C5Q00202Q000C000C00094Q000C000C000800102Q000B000E000C4Q0009000B000100067F00040025000100020004463Q002500010012FD0004000B3Q00201400040004000F2Q0052000500033Q00020B00066Q00240004000600014Q00048Q000500083Q00122Q000600103Q00122Q000700113Q00122Q000800123Q00122Q000900133Q00122Q000A00143Q00122Q000B00153Q00122Q000C00163Q00122Q000D00176Q0005000800010012FD000600084Q0052000700035Q000106000200080004463Q005200010012FD000B000B3Q002014000B000B000C2Q0052000C00044Q003F000D000500090006EE000D004E000100010004463Q004E00012Q0052000D00093Q00128D000E00184Q00D4000D000D000E00128D000E00193Q002014000F000A000D2Q00D4000D000D000F2Q002E000B000D000100067F00060045000100020004463Q004500012Q00AB000600023Q00201400060006001A00060B0106005D00013Q0004463Q005D00010012FD0006001B3Q00061001070001000100022Q00AB3Q00024Q00523Q00044Q00730006000200012Q00AB000600014Q00DF00073Q000300302Q00070003000400302Q00070005001C00302Q0007000700024Q0006000200016Q00013Q00023Q00013Q0003013Q007002083Q00201400023Q000100201400030001000100062F01030005000100020004463Q000500012Q00ED00026Q0016000200014Q0047000200024Q00B23Q00017Q00063Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403013Q002003053Q007461626C6503063Q00636F6E63617403023Q002Q20000C4Q00EC7Q00206Q000100206Q000200122Q000200033Q00122Q000300043Q00202Q0003000300054Q000400013Q00122Q000500066Q0003000500024Q0002000200036Q000200016Q00017Q00093Q00030D3Q004D6F625072696F726974696573030D3Q005072696F726974794C6162656C03053Q007063612Q6C03053Q005469746C6503083Q005072696F7269747903073Q00436F6E74656E7403123Q005072696F72697469657320636C656172656403083Q004475726174696F6E027Q004000124Q008C9Q0000015Q00104Q000100016Q00013Q00206Q000200064Q000B00013Q0004463Q000B00010012FD3Q00033Q0006102Q013Q000100012Q00AB3Q00014Q00733Q000200012Q00AB3Q00024Q00DF00013Q000300302Q00010004000500302Q00010006000700302Q0001000800096Q000200016Q00013Q00013Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q00536574031C3Q002053656C65637420322B206D6F627320666F72207072696F7269747900064Q002Q016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00093Q00030A3Q00466C696768744D6F646503043Q007479706503053Q007461626C65026Q00F03F030F3Q0042656C6F7744657363656E64696E670100030C3Q0043752Q72656E745068617365028Q0003193Q0020466C69676874204D6F6465206368616E67656420746F3A2001164Q006A00015Q00122Q000200026Q00038Q00020002000200262Q00020009000100030004463Q0009000100201400023Q00040006EE0002000A000100010004463Q000A00012Q005200025Q0010150001000100022Q00DD000100013Q00302Q0001000500064Q000100013Q00302Q0001000700084Q000100023Q00122Q000200096Q00035Q00202Q0003000300014Q0002000200034Q0001000200016Q00017Q00063Q00030A3Q0043616D6572614D6F646503043Q007479706503053Q007461626C65026Q00F03F03083Q004175746F4661726D03193Q002043616D657261204D6F6465206368616E67656420746F3A20011A4Q006A00015Q00122Q000200026Q00038Q00020002000200262Q00020009000100030004463Q0009000100201400023Q00040006EE0002000A000100010004463Q000A00012Q005200025Q0010150001000100022Q00AB00015Q00201400010001000500060B2Q01001300013Q0004463Q001300012Q00AB000100014Q00BA0001000100012Q00AB000100024Q00BA0001000100012Q00AB000100033Q001299000200066Q00035Q00202Q0003000300014Q0002000200034Q0001000200016Q00017Q00013Q00030B3Q005A6F6E65456E61626C656401054Q006200015Q00102Q000100016Q000100016Q0001000100016Q00017Q000D3Q00030B3Q004C6F63616C506C6179657203093Q00436861726163746572030A3Q005A6F6E6543656E74657203013Q005803083Q00506F736974696F6E03013Q005903013Q005A03053Q005469746C6503043Q005A6F6E6503073Q00436F6E74656E74030B3Q0043656E746572207365742103083Q004475726174696F6E027Q0040001E4Q00AB7Q0020145Q00010006DC0001000700013Q0004463Q000700012Q00AB000100013Q00201400023Q00022Q000E2Q010002000200060B2Q01001D00013Q0004463Q001D00012Q00AB000200024Q000C00033Q000300202Q00040001000500202Q00040004000400102Q00030004000400202Q00040001000500202Q00040004000600102Q00030006000400202Q00040001000500202Q00040004000700102Q00030007000400102Q0002000300034Q000200036Q0002000100014Q000200046Q00033Q000300302Q00030008000900302Q0003000A000B00302Q0003000C000D4Q0002000200012Q00B23Q00017Q00053Q0003083Q005A6F6E654C656674027Q004003093Q005A6F6E65526967687403093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B010F4Q004100015Q00202Q00023Q000200102Q0001000100024Q00015Q00202Q00023Q000200102Q0001000300024Q00015Q00202Q00023Q000200102Q0001000400024Q00015Q00202Q00023Q000200102Q0001000500024Q000100016Q0001000100016Q00017Q00203Q0003053Q007072696E74031C3Q005B4661726D5D2046752Q6C20526573657420537461727465643Q2E03083Q004175746F4661726D010003053Q00706169727303043Q007479706503053Q007461626C65030D3Q0043752Q72656E7454617267657400030C3Q0043752Q72656E745068617365028Q00030A3Q00536B69704672616D6573030F3Q0042656C6F7744657363656E64696E6703123Q004F726967696E616C43616D6572615479706503113Q004F726967696E616C43616D65726152656603103Q0043616D657261436F2Q6E656374696F6E03103Q0053652Q73696F6E537461727454696D65030A3Q00546F74616C4B692Q6C7303133Q004C6173744D61696E74656E616E636554696D6503103Q004D61696E74656E616E6365436F756E74031A3Q004C6173744D61696E74656E616E6365412Q7461636B436F756E74030C3Q004C617374506F736974696F6E030C3Q00537475636B436F756E746572030E3Q004C6173744C2Q6F6B546172676574030E3Q004C61737454726176656C4C2Q6F6B030C3Q004C617374542Q6F6C5761726E030F3Q004C6173745265667265736854696D65030D3Q004C617374546172676574506F7303113Q004C617374546172676574506F7354696D6503053Q007063612Q6C030D3Q004D6F625072696F726974696573033E3Q005B4661726D5D2046752Q6C20526573657420436F6D706C657465202D20412Q6C2073652Q74696E677320726573746F72656420746F2064656661756C747300833Q001207012Q00013Q00122Q000100028Q000200019Q0000304Q000300046Q00018Q0001000100124Q00056Q000100028Q0002000200044Q001F00010012FD000500064Q0052000600044Q000E0105000200020026AC0005001D000100070004463Q001D00012Q00AB00056Q00C200068Q00050003000600122Q000500056Q000600046Q00050002000700044Q001A00012Q00AB000A6Q003F000A000A00032Q00C0000A0008000900067F00050017000100020004463Q001700010004463Q001F00012Q00AB00056Q00C000050003000400067F3Q000B000100020004463Q000B00012Q00AB3Q00033Q0030F83Q000800096Q00033Q00304Q000A000B6Q00033Q00304Q000C000B6Q00033Q00304Q000D00046Q00033Q00304Q000E00096Q00033Q00304Q000F00096Q00033Q00304Q001000096Q00033Q00304Q0011000B6Q00033Q00304Q0012000B6Q00033Q00304Q0013000B6Q00033Q00304Q0014000B6Q00033Q00304Q0015000B6Q00033Q00304Q001600096Q00033Q00304Q0017000B6Q00033Q00304Q001800096Q00033Q00304Q001900096Q00033Q00304Q001A00096Q00033Q00304Q001B000B6Q00033Q00304Q001C00096Q00033Q00304Q001D000B00124Q001E3Q0006102Q013Q000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q0006102Q010001000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q0006102Q010002000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q0006102Q010003000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q0006102Q010004000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q0006102Q010005000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q0006102Q010006000100012Q00AB3Q00044Q000F012Q000200019Q004Q00015Q00104Q001F000100124Q001E3Q0006102Q010007000100022Q00AB3Q00044Q00AB3Q00024Q00733Q000200010012FD3Q001E3Q0006102Q010008000100022Q00AB3Q00044Q00AB3Q00024Q00733Q000200010012FD3Q001E3Q0006102Q010009000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q0006102Q01000A000100012Q00AB3Q00044Q00733Q000200010012FD3Q001E3Q00020B0001000B4Q009E3Q000200016Q00058Q0001000100124Q00013Q00122Q000100208Q000200016Q00013Q000C3Q00023Q00030E3Q004175746F4661726D546F2Q676C652Q033Q0053657400064Q00C37Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030B3Q004465627567546F2Q676C652Q033Q0053657400064Q00C37Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030B3Q004D6F6244726F70646F776E2Q033Q0053657400064Q00037Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030E3Q005072696F72697479546F2Q676C652Q033Q0053657400064Q00C37Q00206Q000100206Q00024Q000200018Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q00536574031C3Q002053656C65637420322B206D6F627320666F72207072696F7269747900064Q002Q016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00023Q0003113Q00426C61636B6C69737444726F70646F776E2Q033Q0053657400064Q00037Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q0003113Q0049676E6F7265496E76756C546F2Q676C652Q033Q0053657400064Q00C37Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003123Q00466C696768744D6F646544726F70646F776E2Q033Q00536574030A3Q00466C696768744D6F646500094Q0016016Q00206Q000100206Q00024Q000200016Q000300013Q00202Q0003000300034Q0002000100012Q002E3Q000200012Q00B23Q00017Q00033Q0003123Q0043616D6572614D6F646544726F70646F776E2Q033Q00536574030A3Q0043616D6572614D6F646500094Q0016016Q00206Q000100206Q00024Q000200016Q000300013Q00202Q0003000300034Q0002000100012Q002E3Q000200012Q00B23Q00017Q00023Q00030A3Q005A6F6E65546F2Q676C652Q033Q0053657400064Q00C37Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q00030E3Q005A6F6E6553697A65536C696465722Q033Q00536574026Q00494000064Q002Q016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003023Q005F4703053Q00466F726765030D3Q005265736574506C617965725549000A3Q0012FD3Q00013Q0020145Q00020020145Q000300060B012Q000900013Q0004463Q000900010012FD3Q00013Q0020145Q00020020145Q00032Q00BA3Q000100012Q00B23Q00017Q00043Q0003083Q004175746F4661726D0100030E3Q004175746F4661726D546F2Q676C6503053Q007063612Q6C00154Q00AB7Q0020145Q00010006EE3Q0008000100010004463Q000800012Q00AB3Q00013Q0006EE3Q0008000100010004463Q000800012Q00B23Q00014Q00AB7Q0030613Q000100026Q00028Q000100016Q00033Q00206Q000300064Q001400013Q0004463Q001400010012FD3Q00043Q0006102Q013Q000100012Q00AB3Q00034Q00733Q000200012Q00B23Q00013Q00013Q00023Q00030E3Q004175746F4661726D546F2Q676C652Q033Q0053657400064Q00C37Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00", GetFEnv(), ...);
