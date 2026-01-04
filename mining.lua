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
				if (Enum <= 212) then
					if (Enum <= 105) then
						if (Enum <= 52) then
							if (Enum <= 25) then
								if (Enum <= 12) then
									if (Enum <= 5) then
										if (Enum <= 2) then
											if (Enum <= 0) then
												local Results;
												local Edx;
												local Results, Limit;
												local B;
												local A;
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
												Stk[Inst[2]] = Env[Inst[3]];
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
											elseif (Enum == 1) then
												local B;
												local T;
												local A;
												Stk[Inst[2]] = {};
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = {};
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
												Stk[Inst[2]][Inst[3]] = Inst[4];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = {};
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												T = Stk[A];
												B = Inst[3];
												for Idx = 1, B do
													T[Idx] = Stk[A + Idx];
												end
											else
												local A;
												A = Inst[2];
												Stk[A] = Stk[A]();
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
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
												if (Inst[2] < Stk[Inst[4]]) then
													VIP = VIP + 1;
												else
													VIP = Inst[3];
												end
											end
										elseif (Enum <= 3) then
											local B;
											local T;
											local A;
											Stk[Inst[2]] = Inst[3];
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
											A = Inst[2];
											T = Stk[A];
											B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										elseif (Enum == 4) then
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
											if not Stk[Inst[2]] then
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
									elseif (Enum <= 8) then
										if (Enum <= 6) then
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
										elseif (Enum > 7) then
											local B;
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
											B = Stk[Inst[4]];
											if B then
												VIP = VIP + 1;
											else
												Stk[Inst[2]] = B;
												VIP = Inst[3];
											end
										else
											local A = Inst[2];
											local T = Stk[A];
											for Idx = A + 1, Inst[3] do
												Insert(T, Stk[Idx]);
											end
										end
									elseif (Enum <= 10) then
										if (Enum > 9) then
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
											Stk[Inst[2]] = Inst[3] ~= 0;
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
											Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										end
									elseif (Enum == 11) then
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
										if (Stk[Inst[2]] < Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local Edx;
										local Results, Limit;
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
										Stk[Inst[2]] = Upvalues[Inst[3]];
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
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 18) then
									if (Enum <= 15) then
										if (Enum <= 13) then
											Stk[Inst[2]][Inst[3]] = Inst[4];
										elseif (Enum > 14) then
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
											do
												return Stk[Inst[2]];
											end
										else
											local Edx;
											local Results, Limit;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
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
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
									elseif (Enum <= 16) then
										Stk[Inst[2]] = -Stk[Inst[3]];
									elseif (Enum > 17) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										local A = Inst[2];
										Stk[A] = Stk[A]();
									end
								elseif (Enum <= 21) then
									if (Enum <= 19) then
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
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 20) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
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
										if (Stk[Inst[2]] ~= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
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
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
										do
											return Stk[Inst[2]];
										end
									end
								elseif (Enum <= 23) then
									if (Enum == 22) then
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
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
										local Results;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
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
								elseif (Enum == 24) then
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
									do
										return;
									end
								else
									local B;
									local T;
									local A;
									Stk[Inst[2]] = {};
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
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 38) then
								if (Enum <= 31) then
									if (Enum <= 28) then
										if (Enum <= 26) then
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
										elseif (Enum == 27) then
											local A;
											Stk[Inst[2]]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
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
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Inst[2] < Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local Edx;
											local Results;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
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
									elseif (Enum <= 29) then
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
									elseif (Enum > 30) then
										local A;
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
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 34) then
									if (Enum <= 32) then
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
									elseif (Enum == 33) then
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
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
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
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
									end
								elseif (Enum <= 36) then
									if (Enum == 35) then
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										local A;
										Stk[Inst[2]][Inst[3]] = Inst[4];
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
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum > 37) then
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
									if (Stk[Inst[2]] <= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 45) then
								if (Enum <= 41) then
									if (Enum <= 39) then
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
									elseif (Enum > 40) then
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
										local A;
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
									end
								elseif (Enum <= 43) then
									if (Enum == 42) then
										local A = Inst[2];
										local B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Stk[Inst[4]]];
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
								elseif (Enum == 44) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								end
							elseif (Enum <= 48) then
								if (Enum <= 46) then
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
								elseif (Enum == 47) then
									local T;
									local K;
									local B;
									local A;
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
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
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
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 50) then
								if (Enum == 49) then
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
								else
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 51) then
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
								do
									return;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 78) then
							if (Enum <= 65) then
								if (Enum <= 58) then
									if (Enum <= 55) then
										if (Enum <= 53) then
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
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Stk[Inst[2]] < Inst[4]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum > 54) then
											local A;
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
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
									elseif (Enum <= 56) then
										local A = Inst[2];
										local B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									elseif (Enum > 57) then
										do
											return Stk[Inst[2]];
										end
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
								elseif (Enum <= 61) then
									if (Enum <= 59) then
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									elseif (Enum > 60) then
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
										Stk[Inst[2]] = Stk[Inst[3]];
									end
								elseif (Enum <= 63) then
									if (Enum == 62) then
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
									else
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									end
								elseif (Enum == 64) then
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
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
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
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 71) then
								if (Enum <= 68) then
									if (Enum <= 66) then
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
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 67) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
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
										VIP = Inst[3];
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
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 69) then
									local A;
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
									A = Inst[2];
									Stk[A] = Stk[A]();
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
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 70) then
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
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
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum <= 74) then
								if (Enum <= 72) then
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
								elseif (Enum > 73) then
									local A;
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
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 76) then
								if (Enum > 75) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Stk[Inst[2]] > Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = VIP + Inst[3];
								end
							elseif (Enum == 77) then
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
								do
									return;
								end
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
						elseif (Enum <= 91) then
							if (Enum <= 84) then
								if (Enum <= 81) then
									if (Enum <= 79) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									elseif (Enum > 80) then
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
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
										Stk[Inst[2]] = Inst[3];
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
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 82) then
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
								elseif (Enum == 83) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
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
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 87) then
								if (Enum <= 85) then
									local DIP;
									local NStk;
									local Upv;
									local List;
									local Cls;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
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
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Cls = {};
									for Idx = 1, #Lupvals do
										List = Lupvals[Idx];
										for Idz = 0, #List do
											Upv = List[Idz];
											NStk = Upv[1];
											DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum == 86) then
									local A;
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
								end
							elseif (Enum <= 89) then
								if (Enum == 88) then
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
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 90) then
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
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
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
						elseif (Enum <= 98) then
							if (Enum <= 94) then
								if (Enum <= 92) then
									local A;
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
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 93) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
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
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 96) then
								if (Enum == 95) then
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
								end
							elseif (Enum == 97) then
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
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
						elseif (Enum <= 101) then
							if (Enum <= 99) then
								local A;
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Enum == 100) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
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
							end
						elseif (Enum <= 103) then
							if (Enum > 102) then
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
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 104) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						end
					elseif (Enum <= 158) then
						if (Enum <= 131) then
							if (Enum <= 118) then
								if (Enum <= 111) then
									if (Enum <= 108) then
										if (Enum <= 106) then
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
											Stk[Inst[2]] = #Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Inst[2] < Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum == 107) then
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
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Stk[Inst[2]] < Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
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
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
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
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
										end
									elseif (Enum <= 109) then
										VIP = Inst[3];
									elseif (Enum > 110) then
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
										Stk[Inst[2]] = -Stk[Inst[3]];
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
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									else
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
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
								elseif (Enum <= 114) then
									if (Enum <= 112) then
										local A;
										local K;
										local B;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
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
										Stk[Inst[2]] = Env[Inst[3]];
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
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 113) then
										local B;
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
										B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
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
								elseif (Enum <= 116) then
									if (Enum == 115) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										local T;
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
										Stk[Inst[2]] = {};
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
								elseif (Enum == 117) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
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
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
							elseif (Enum <= 124) then
								if (Enum <= 121) then
									if (Enum <= 119) then
										local A;
										Stk[Inst[2]] = Inst[3] ~= 0;
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
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 120) then
										local Edx;
										local Results;
										local A;
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
								elseif (Enum <= 122) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								elseif (Enum > 123) then
									local Edx;
									local Results, Limit;
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
								else
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 127) then
								if (Enum <= 125) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 126) then
									local Edx;
									local Results;
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
									Stk[Inst[2]] = Stk[Inst[3]];
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
							elseif (Enum <= 129) then
								if (Enum == 128) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
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
							elseif (Enum > 130) then
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
						elseif (Enum <= 144) then
							if (Enum <= 137) then
								if (Enum <= 134) then
									if (Enum <= 132) then
										local A;
										A = Inst[2];
										Stk[A] = Stk[A]();
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
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 133) then
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
									else
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
									end
								elseif (Enum <= 135) then
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
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
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
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								elseif (Enum == 136) then
									local B;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
									Stk[Inst[2]] = Inst[3];
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
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 140) then
								if (Enum <= 138) then
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
								elseif (Enum == 139) then
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
									Stk[Inst[2]]();
								end
							elseif (Enum <= 142) then
								if (Enum > 141) then
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
									Stk[Inst[2]] = {};
								end
							elseif (Enum > 143) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
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
						elseif (Enum <= 151) then
							if (Enum <= 147) then
								if (Enum <= 145) then
									local K;
									local B;
									local A;
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
								elseif (Enum > 146) then
									local B;
									local A;
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								else
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
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 149) then
								if (Enum > 148) then
									local A;
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
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
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
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum == 150) then
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
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 154) then
							if (Enum <= 152) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
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
							elseif (Enum > 153) then
								local Edx;
								local Results, Limit;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								Stk[A](Unpack(Stk, A + 1, Top));
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
						elseif (Enum <= 156) then
							if (Enum > 155) then
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
							else
								local Edx;
								local Results, Limit;
								local A;
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
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
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
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
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
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 157) then
							local K;
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
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							local A;
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
						end
					elseif (Enum <= 185) then
						if (Enum <= 171) then
							if (Enum <= 164) then
								if (Enum <= 161) then
									if (Enum <= 159) then
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
									elseif (Enum == 160) then
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
									end
								elseif (Enum <= 162) then
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
									do
										return;
									end
								elseif (Enum > 163) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									do
										return;
									end
								end
							elseif (Enum <= 167) then
								if (Enum <= 165) then
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 166) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
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
								else
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								end
							elseif (Enum <= 169) then
								if (Enum == 168) then
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
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
								end
							elseif (Enum > 170) then
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
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
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
							end
						elseif (Enum <= 178) then
							if (Enum <= 174) then
								if (Enum <= 172) then
									local K;
									local B;
									local A;
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
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 173) then
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
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
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
							elseif (Enum <= 176) then
								if (Enum > 175) then
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
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum == 177) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
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
						elseif (Enum <= 181) then
							if (Enum <= 179) then
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 180) then
								if Stk[Inst[2]] then
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
						elseif (Enum <= 183) then
							if (Enum == 182) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
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
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 184) then
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
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
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
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
					elseif (Enum <= 198) then
						if (Enum <= 191) then
							if (Enum <= 188) then
								if (Enum <= 186) then
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
								elseif (Enum == 187) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
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
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								end
							elseif (Enum <= 189) then
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
							elseif (Enum == 190) then
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
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
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
						elseif (Enum <= 194) then
							if (Enum <= 192) then
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 193) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
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
							end
						elseif (Enum <= 196) then
							if (Enum == 195) then
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
								Stk[Inst[2]] = {};
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
							else
								do
									return;
								end
							end
						elseif (Enum == 197) then
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
						end
					elseif (Enum <= 205) then
						if (Enum <= 201) then
							if (Enum <= 199) then
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
							elseif (Enum > 200) then
								local A;
								local K;
								local B;
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
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
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
							end
						elseif (Enum <= 203) then
							if (Enum == 202) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							else
								local T;
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
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum > 204) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
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
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 208) then
						if (Enum <= 206) then
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
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 207) then
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
						end
					elseif (Enum <= 210) then
						if (Enum > 209) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
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
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum == 211) then
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
						Stk[Inst[2]] = Upvalues[Inst[3]];
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
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
						VIP = Inst[3];
					else
						VIP = VIP + 1;
					end
				elseif (Enum <= 318) then
					if (Enum <= 265) then
						if (Enum <= 238) then
							if (Enum <= 225) then
								if (Enum <= 218) then
									if (Enum <= 215) then
										if (Enum <= 213) then
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										elseif (Enum == 214) then
											local A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										else
											Upvalues[Inst[3]] = Stk[Inst[2]];
										end
									elseif (Enum <= 216) then
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 217) then
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
									else
										local A;
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
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 221) then
									if (Enum <= 219) then
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
									elseif (Enum == 220) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Inst[2] < Stk[Inst[4]]) then
											VIP = Inst[3];
										else
											VIP = VIP + 1;
										end
									end
								elseif (Enum <= 223) then
									if (Enum == 222) then
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
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] < Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum == 224) then
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
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
								end
							elseif (Enum <= 231) then
								if (Enum <= 228) then
									if (Enum <= 226) then
										local A;
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
									elseif (Enum > 227) then
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
										Stk[Inst[2]][Inst[3]] = Inst[4];
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
									end
								elseif (Enum <= 229) then
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
								elseif (Enum > 230) then
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
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local Edx;
									local Results, Limit;
									local A;
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum <= 234) then
								if (Enum <= 232) then
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
								elseif (Enum > 233) then
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
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
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
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								end
							elseif (Enum <= 236) then
								if (Enum > 235) then
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
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 237) then
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
							end
						elseif (Enum <= 251) then
							if (Enum <= 244) then
								if (Enum <= 241) then
									if (Enum <= 239) then
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
									elseif (Enum == 240) then
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
									else
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
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
										Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Enum <= 242) then
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
								elseif (Enum > 243) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
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
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
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
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
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
							elseif (Enum <= 247) then
								if (Enum <= 245) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								elseif (Enum == 246) then
									local Edx;
									local Results;
									local A;
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
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
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								end
							elseif (Enum <= 249) then
								if (Enum == 248) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Stk[Inst[4]]];
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
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
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
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 250) then
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
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
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 258) then
							if (Enum <= 254) then
								if (Enum <= 252) then
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
								elseif (Enum == 253) then
									local K;
									local B;
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
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
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
								else
									local B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 256) then
								if (Enum == 255) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
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
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum == 257) then
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
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 261) then
							if (Enum <= 259) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 260) then
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
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 263) then
							if (Enum == 262) then
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
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
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
							end
						elseif (Enum > 264) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
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
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 291) then
						if (Enum <= 278) then
							if (Enum <= 271) then
								if (Enum <= 268) then
									if (Enum <= 266) then
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
									elseif (Enum > 267) then
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
									end
								elseif (Enum <= 269) then
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
								elseif (Enum == 270) then
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
								else
									local A = Inst[2];
									do
										return Stk[A], Stk[A + 1];
									end
								end
							elseif (Enum <= 274) then
								if (Enum <= 272) then
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum > 273) then
									Stk[Inst[2]] = Inst[3] ~= 0;
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
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 276) then
								if (Enum == 275) then
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
								else
									local T;
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
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
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
							elseif (Enum == 277) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
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
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 284) then
							if (Enum <= 281) then
								if (Enum <= 279) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
								elseif (Enum == 280) then
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
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 282) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 283) then
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							else
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 287) then
							if (Enum <= 285) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
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
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 286) then
								local Edx;
								local Results;
								local A;
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local T;
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
								Stk[Inst[2]] = {};
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
						elseif (Enum <= 289) then
							if (Enum > 288) then
								local K;
								local B;
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
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum == 290) then
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 304) then
						if (Enum <= 297) then
							if (Enum <= 294) then
								if (Enum <= 292) then
									local A;
									local K;
									local B;
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
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum == 293) then
									Stk[Inst[2]] = Inst[3];
								else
									local Step;
									local Index;
									local A;
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
									A = Inst[2];
									Index = Stk[A];
									Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum <= 295) then
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
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Enum == 296) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
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
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 300) then
							if (Enum <= 298) then
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
							elseif (Enum > 299) then
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
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
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 302) then
							if (Enum == 301) then
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
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
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
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum == 303) then
							local T;
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
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
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
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 311) then
						if (Enum <= 307) then
							if (Enum <= 305) then
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
							elseif (Enum == 306) then
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
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
						elseif (Enum <= 309) then
							if (Enum > 308) then
								Stk[Inst[2]] = {};
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
								Stk[Inst[2]] = {};
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
							else
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							end
						elseif (Enum == 310) then
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
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 314) then
						if (Enum <= 312) then
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 313) then
							local B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							local T;
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
							Stk[Inst[2]] = {};
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
					elseif (Enum <= 316) then
						if (Enum > 315) then
							local A;
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
						end
					elseif (Enum > 317) then
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
					else
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
					end
				elseif (Enum <= 371) then
					if (Enum <= 344) then
						if (Enum <= 331) then
							if (Enum <= 324) then
								if (Enum <= 321) then
									if (Enum <= 319) then
										local B;
										local T;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
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
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									elseif (Enum == 320) then
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local Edx;
										local Results, Limit;
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
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 322) then
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
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 323) then
									local A;
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
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 327) then
								if (Enum <= 325) then
									local Edx;
									local Results, Limit;
									local A;
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
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
								elseif (Enum == 326) then
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
									local Edx;
									local Results;
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
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
							elseif (Enum <= 329) then
								if (Enum > 328) then
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
								else
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
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 330) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
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
								Stk[Inst[2]] = Stk[Inst[3]];
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
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 337) then
							if (Enum <= 334) then
								if (Enum <= 332) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
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
									if (Stk[Inst[2]] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 333) then
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
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
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
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 335) then
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
							elseif (Enum > 336) then
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
						elseif (Enum <= 340) then
							if (Enum <= 338) then
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
								VIP = Inst[3];
							elseif (Enum == 339) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum <= 342) then
							if (Enum == 341) then
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
							else
								local B;
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
								Stk[Inst[2]][Inst[3]] = Inst[4];
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
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
								Stk[Inst[2]] = {};
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
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum > 343) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
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
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
						end
					elseif (Enum <= 357) then
						if (Enum <= 350) then
							if (Enum <= 347) then
								if (Enum <= 345) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
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
								elseif (Enum == 346) then
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
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
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
								end
							elseif (Enum <= 348) then
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
							elseif (Enum > 349) then
								local B;
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
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
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
							end
						elseif (Enum <= 353) then
							if (Enum <= 351) then
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							elseif (Enum == 352) then
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
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								local K;
								local B;
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
						elseif (Enum <= 355) then
							if (Enum == 354) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
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
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 356) then
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
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
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
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
						end
					elseif (Enum <= 364) then
						if (Enum <= 360) then
							if (Enum <= 358) then
								local Edx;
								local Results, Limit;
								local B;
								local A;
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
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 359) then
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
							else
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
							end
						elseif (Enum <= 362) then
							if (Enum == 361) then
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 363) then
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
								if (Mvm[1] == 60) then
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
					elseif (Enum <= 367) then
						if (Enum <= 365) then
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
							VIP = Inst[3];
						elseif (Enum == 366) then
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
					elseif (Enum <= 369) then
						if (Enum > 368) then
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
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum > 370) then
						local A;
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
						if (Stk[Inst[2]] < Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
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
					end
				elseif (Enum <= 398) then
					if (Enum <= 384) then
						if (Enum <= 377) then
							if (Enum <= 374) then
								if (Enum <= 372) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
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
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								elseif (Enum > 373) then
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
							elseif (Enum <= 375) then
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
							elseif (Enum == 376) then
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
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
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
						elseif (Enum <= 380) then
							if (Enum <= 378) then
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
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 379) then
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
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 382) then
							if (Enum == 381) then
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
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
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
							end
						elseif (Enum == 383) then
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
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 391) then
						if (Enum <= 387) then
							if (Enum <= 385) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum > 386) then
								local A;
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
							end
						elseif (Enum <= 389) then
							if (Enum > 388) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
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
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Stk[Inst[2]] > Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 390) then
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
						end
					elseif (Enum <= 394) then
						if (Enum <= 392) then
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
							Stk[Inst[2]][Inst[3]] = Inst[4];
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
						elseif (Enum == 393) then
							local K;
							local B;
							local A;
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
							Stk[Inst[2]] = Inst[3];
						else
							local A;
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
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
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
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
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
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 396) then
						if (Enum == 395) then
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
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
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
					elseif (Enum == 397) then
						local A;
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
				elseif (Enum <= 411) then
					if (Enum <= 404) then
						if (Enum <= 401) then
							if (Enum <= 399) then
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 400) then
								local Results;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
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
								Stk[Inst[2]] = Stk[Inst[3]];
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
							end
						elseif (Enum <= 402) then
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
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 403) then
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
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 407) then
						if (Enum <= 405) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 406) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
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
						else
							local A;
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
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
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 409) then
						if (Enum == 408) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
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
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
					elseif (Enum > 410) then
						local K;
						local B;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
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
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 418) then
					if (Enum <= 414) then
						if (Enum <= 412) then
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
						elseif (Enum == 413) then
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
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
							Stk[Inst[2]] = Stk[Inst[3]];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 416) then
						if (Enum == 415) then
							local Results;
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
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
					elseif (Enum == 417) then
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
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
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 421) then
					if (Enum <= 419) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 420) then
						local A;
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Upvalues[Inst[3]] = Stk[Inst[2]];
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
					else
						local A;
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					end
				elseif (Enum <= 423) then
					if (Enum == 422) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					elseif (Stk[Inst[2]] ~= Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum == 424) then
					if (Inst[2] < Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				else
					local A;
					Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
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
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!7C012Q0003043Q007469636B03023Q005F4703053Q00466F72676503043Q005461627303063Q004D696E696E67026Q003E4003043Q007761726E03433Q005B466F726765204D696E696E675D2054696D656F75742077616974696E6720666F7220466F7267652E4D696E696E67207461623B2061626F7274696E67206C6F61642E03043Q007461736B03043Q0077616974026Q00E03F03043Q0067616D65030A3Q004765745365727669636503073Q00506C6179657273030A3Q0052756E5365727669636503113Q005265706C69636174656453746F7261676503093Q00576F726B7370616365030B3Q004C6F63616C506C6179657203083Q005261796669656C64030A3Q004175746F4D696E696E670100030D3Q0053656C65637465644172656173030D3Q0053656C6563746564526F636B73030C3Q0053656C65637465644F726573030E3Q00526F636B5072696F726974696573030F3Q005072696F72697479456E61626C65642Q0103143Q005072696F726974795363616E496E74657276616C029A5Q99B93F03163Q005072696F72697479537769746368432Q6F6C646F776E026Q00F03F03143Q005072696F72697479536B6970432Q6F6C646F776E026Q00204003113Q005072696F726974794477652Q6C54696D65026Q001040030E3Q00526F636B4F726546696C7465727303043Q00526F636B0003043Q004F72657303093Q0044656275674D6F646503083Q0044697374616E6365026Q00184003093Q004D696E6544656C617903063Q00486569676874029A5Q991D40030A3Q00466C696768744D6F646503053Q0042656C6F77030A3Q0047686F737453702Q6564026Q003940030B3Q0047686F73744F2Q66736574026Q000CC0030B3Q004D696E696E6752616E6765025Q00409F4003133Q00446972656374436861736544697374616E6365025Q00C07240030B3Q005A6F6E65456E61626C6564030A3Q005A6F6E6543656E74657203013Q0058028Q0003013Q005903013Q005A03083Q005A6F6E654C65667403093Q005A6F6E65526967687403093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B03063Q005A6F6E655570026Q002E4003083Q005A6F6E65446F776E026Q00144003123Q004D61696E74656E616E6365456E61626C656403133Q004D61696E74656E616E6365496E74657276616C026Q004E4003183Q004D61696E74656E616E63654D696E655468726573686F6C64026Q00794003093Q0053702Q65644E656172029A5Q99E93F030B3Q0053702Q6564536C6F776D6F026Q330740030D3Q0053702Q6564412Q70726F61636803083Q0053702Q6564466172026Q00F83F03113Q005361666548656967687444656661756C74025Q00806640030F3Q0053616665486569676874537061776E030E3Q005361666548656967687449646C6503103Q00537061776E436865636B526164697573025Q00407F4003103Q00526F746174696F6E446561645A6F6E65026Q000C40030F3Q004F7265436865636B456E61626C6564030D3Q004F7265436865636B4C6576656C026Q004440030D3Q004F7265536B69704E6F7469667903143Q00412Q6C6F774F726546696C746572427970612Q7303113Q00557365476C6F62616C46612Q6C6261636B03133Q00526F636B52656672657368496E74657276616C03183Q00526F636B526566726573684E6F54617267657444656C6179026Q000440030A3Q0043616D6572614D6F6465030A3Q004C6F636B546172676574030C3Q0043616D657261486569676874026Q004240030E3Q0043616D65726144697374616E6365026Q002440030A3Q0043616D6572615369646503193Q004175746F5472696D496E76616C696453656C656374696F6E7303103Q00486F72697A6F6E74616C4F2Q6673657403163Q00526F746174696F6E446561645A6F6E6554726176656C030F3Q004D696E6544656C61794A692Q746572026Q00D03F030E3Q00537475636B446574656374696F6E03073Q00456E61626C6564030B3Q005468726573686F6C644C31030B3Q005468726573686F6C644C32026Q004940030B3Q005468726573686F6C644C33026Q005440030D3Q0054696D655468726573686F6C64026Q003440030E3Q00476C6974636844697374616E6365026Q001C4003103Q005265636F76657279432Q6F6C646F776E03113Q00506F736974696F6E5468726573686F6C6403153Q00506F736974696F6E436865636B496E74657276616C026Q00084003053Q00706169727303043Q007479706503053Q007461626C65030B3Q0043752Q72656E74526F636B030C3Q0043752Q72656E745068617365030A3Q00536B69704672616D6573030E3Q00536B69704D696E654672616D6573030D3Q004C6F636B65644D696E65506F73030E3Q004C617374526F636B536561726368030D3Q004C6173744E6F526F636B4C6F6703103Q0053652Q73696F6E537461727454696D65030A3Q00546F74616C4D696E656403133Q004C6173744D61696E74656E616E636554696D6503103Q004D61696E74656E616E6365436F756E74030E3Q004C6173744C2Q6F6B546172676574030C3Q00536B692Q706564526F636B73030D3Q004C617374536B6970526573657403103Q004C61737446696C746572536F75726365030E3Q004C61737446696C746572526F636B03113Q004C6173744F7265536B69704E6F74696679030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B73030F3Q004C617374526F636B52656672657368030D3Q004E6F54617267657453696E636503153Q0049676E6F72654F726546696C74657273556E74696C03123Q004C6173745072696F7269747953776974636803113Q005072696F726974794C6F636B556E74696C03143Q004C6173745072696F72697479526F636B5479706503153Q005072696F7269747954797065432Q6F6C646F776E7303123Q0043616D6572615368616B65526573746F726503153Q004C617374416C72656164794D696E696E6754696D65030D3Q0050656E64696E6753776974636803113Q004C61737450656E64696E6753776974636803123Q004F726967696E616C43616D6572615479706503103Q0043616D657261436F2Q6E656374696F6E030A3Q004C617374526F636B4850030B3Q004C617374526F636B52656603123Q004D696E657353696E636548504368616E6765030E3Q00537475636B436865636B54696D65030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D65030E3Q004C32412Q74656D7074436F756E74030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D65030F3Q005072696F72697479536C696465727303113Q004C6173745072696F72697479436865636B03143Q004C61737454726176656C4C2Q6F6B54617267657403053Q00417265617303053Q00526F636B73030C3Q004D696E696E67436F6E66696703083Q00496E7374616E63652Q033Q006E657703063Q00466F6C64657203063Q0073656C65637403053Q007063612Q6C03073Q0044657374726F79030D3Q0043752Q72656E7443616D657261030D3Q0043726561746553656374696F6E030B3Q004175746F204D696E696E6703103Q004175746F4D696E696E67546F2Q676C65030C3Q00437265617465546F2Q676C6503043Q004E616D6503123Q00456E61626C65204175746F204D696E696E67030C3Q0043752Q72656E7456616C756503043Q00466C616703103Q004D696E696E674175746F546F2Q676C6503083Q0043612Q6C6261636B03143Q00537475636B446574656374696F6E546F2Q676C6503113Q00416E74692D537475636B2053797374656D031A3Q004D696E696E67537475636B446574656374696F6E546F2Q676C65031B3Q00506F736974696F6E436865636B496E74657276616C536C69646572030C3Q00437265617465536C6964657203183Q00537475636B20436865636B20496E74657276616C2028732903053Q0052616E676503093Q00496E6372656D656E7403063Q0053752Q66697803013Q007303183Q004D696E696E67537475636B436865636B496E74657276616C03173Q00506F736974696F6E5468726573686F6C64536C69646572031C3Q00537475636B204D6F7665205468726573686F6C64202873747564732903063Q0020737475647303183Q004D696E696E67537475636B4D6F76655468726573686F6C64030C3Q0043726561746542752Q746F6E030D3Q00466F72636520436C65616E7570030D3Q0053652Q73696F6E205374617473030F3Q004172656120262053652Q74696E677303053Q007072696E7403283Q005B466F726765204D696E696E675D20526F636B20536F757263653A20412Q6C204172656173202D20030B3Q0020726F636B20747970657303293Q005B466F726765204D696E696E675D204F726520536F757263653A20412Q6C2049736C616E6473202D2003053Q00206F726573031C3Q005B466F726765204D696E696E675D20526F636B20536F757263653A2003093Q00206172656173202D20030C3Q004172656144726F70646F776E030E3Q0043726561746544726F70646F776E031B3Q004D696E696E6720417265617320284D756C74692D53656C6563742903073Q004F7074696F6E73030D3Q0043752Q72656E744F7074696F6E030F3Q004D756C7469706C654F7074696F6E73030B3Q004D696E696E67417265617303093Q00417265614C6162656C030B3Q004372656174654C6162656C03013Q002003063Q00636F6E63617403023Q002C2003093Q00412Q6C204172656173030E3Q00205265667265736820417265617303153Q0020436C65617220412Q6C2053656C656374696F6E73030D3Q005265667265736820526F636B73030C3Q0052656672657368204F726573030F3Q00205363616E204172656120496E666F03123Q00466C696768744D6F646544726F70646F776E030B3Q00466C69676874204D6F646503053Q0041626F766503103Q004D696E696E67466C696768744D6F646503123Q0043616D6572614D6F646544726F70646F776E030B3Q0043616D657261204D6F646503043Q004E6F6E65030B3Q0046697865644F2Q6673657403103Q004D696E696E6743616D6572614D6F646503113Q0054696D696E672026204D6F76656D656E74030F3Q004D696E6544656C6179536C69646572031A3Q004D696E652044656C61792028626173652C207365636F6E647329029A5Q99A93F026Q33E33F027B14AE47E17A843F030F3Q004D696E696E674D696E6544656C617903153Q004D696E6544656C61794A692Q746572536C6964657203153Q004D696E652044656C6179204A692Q746572204D6178029A5Q99D93F03153Q004D696E696E674D696E6544656C61794A692Q74657203163Q00486F72697A6F6E74616C4F2Q66736574536C69646572031A3Q00486F72697A6F6E74616C204F2Q66736574202873747261666529026Q0024C003163Q004D696E696E67486F72697A6F6E74616C4F2Q66736574031C3Q00526F746174696F6E446561645A6F6E6554726176656C536C69646572031B3Q00526F746174696F6E2044656164205A6F6E65202874726176656C29031C3Q004D696E696E67526F746174696F6E446561645A6F6E6554726176656C03103Q005461726765742053656C656374696F6E030C3Q00526F636B44726F70646F776E03193Q00526F636B20547970657320284D756C74692D53656C6563742903143Q00284E6F20726F636B7320617661696C61626C6529030B3Q004D696E696E67526F636B7303093Q00526F636B4C6162656C030F3Q00286E6F6E652073656C656374656429030E3Q00526F636B436F756E744C6162656C03203Q00F09F938A202873656C65637420726F636B7320746F20732Q6520636F756E7429030F3Q005072696F726974792053797374656D030E3Q005072696F72697479546F2Q676C65030F3Q00456E61626C65205072696F7269747903143Q004D696E696E675072696F72697479546F2Q676C65030D3Q005072696F726974794C6162656C03203Q002053656C65637420322B20726F636B7320746F20736574207072696F72697479030E3Q002052657665727365204F72646572031A3Q005072696F726974795363616E496E74657276616C536C69646572031A3Q005072696F72697479205363616E20496E74657276616C20287329031A3Q004D696E696E675072696F726974795363616E496E74657276616C031C3Q005072696F72697479537769746368432Q6F6C646F776E536C69646572031C3Q005072696F726974792053776974636820432Q6F6C646F776E20287329031C3Q004D696E696E675072696F72697479537769746368432Q6F6C646F776E03173Q005072696F726974794477652Q6C54696D65536C6964657203173Q005072696F72697479204477652Q6C2054696D652028732903173Q004D696E696E675072696F726974794477652Q6C54696D65031A3Q005072696F72697479536B6970432Q6F6C646F776E536C69646572031A3Q005072696F7269747920536B6970204F6C6420526F636B20287329031A3Q004D696E696E675072696F72697479536B6970432Q6F6C646F776E03103Q00436C656172205072696F726974696573030B3Q004F726544726F70646F776E03163Q00476C6F62616C204F726573202846612Q6C6261636B2903133Q002853656C656374206172656120666972737429030A3Q004D696E696E674F72657303083Q004F72654C6162656C03183Q00476C6F62616C204F726573202866612Q6C6261636B293A2003113Q00436C65617220476C6F62616C204F72657303173Q00557365476C6F62616C46612Q6C6261636B546F2Q676C6503133Q0055736520476C6F62616C2046612Q6C6261636B03173Q004D696E696E67557365476C6F62616C46612Q6C6261636B03113Q0041637469766546696C7465724C6162656C03133Q004163746976652046696C7465723A204E6F6E6503113Q005472696D496E76616C6964546F2Q676C6503233Q004175746F2D7472696D20696E76616C69642073656C656374696F6E732028736166652903153Q004D696E696E674175746F5472696D496E76616C6964031C3Q005065722D526F636B204F72652046696C746572732028536C6F747329030F3Q0046696C746572536C6F7431526F636B030D3Q00536C6F742031202D20526F636B03063Q00286E6F6E652903153Q004D696E696E6746696C746572536C6F7431526F636B030E3Q0046696C746572536C6F74314F7265030D3Q00536C6F742031202D204F72657303143Q004D696E696E6746696C746572536C6F74314F726503103Q0046696C746572536C6F74314C6162656C030B3Q00E286922028656D70747929030F3Q0046696C746572536C6F7432526F636B030D3Q00536C6F742032202D20526F636B03153Q004D696E696E6746696C746572536C6F7432526F636B027Q0040030E3Q0046696C746572536C6F74324F7265030D3Q00536C6F742032202D204F72657303143Q004D696E696E6746696C746572536C6F74324F726503103Q0046696C746572536C6F74324C6162656C030F3Q0046696C746572536C6F7433526F636B030D3Q00536C6F742033202D20526F636B03153Q004D696E696E6746696C746572536C6F7433526F636B030E3Q0046696C746572536C6F74334F7265030D3Q00536C6F742033202D204F72657303143Q004D696E696E6746696C746572536C6F74334F726503103Q0046696C746572536C6F74334C6162656C03163Q00436C65617220412Q6C20536C6F742046696C7465727303243Q0064595A5F20412Q706C7920536C6F742054656D706C6174657320285065722D526F636B29030E3Q00496365202B204C6967687469746503063Q0049636569746503073Q00536E6F7769746503073Q0053616E6374697303083Q0056656C6368697265030C3Q0046726F737420466F2Q73696C03083Q004C6967687469746503113Q0049636520284E6F204C6967687469746529030A3Q0044656D6F6E204172656103083Q0044656D6F6E69746503083Q004461726B7279746503083Q004D61676D6169746503063Q0048656176656E03093Q0048656176656E697465030A3Q0047617267616E7475616E03083Q00537572796166616C030B3Q00457468657265616C69746503093Q00436C65617220412Q6C03133Q004F726554656D706C61746544726F70646F776E03233Q00476C6F62616C204F72652054656D706C617465732028517569636B2053656C6563742903113Q004D696E696E674F726554656D706C617465030E3Q004F7265436865636B546F2Q676C6503233Q00536B697020526F636B206966204F7265204E6F74204D61746368202861742034302529030E3Q004D696E696E674F7265436865636B03133Q004F7265536B69704E6F74696679546F2Q676C6503123Q004E6F74696679206F6E204F726520536B697003133Q004D696E696E674F7265536B69704E6F7469667903153Q004F726546696C746572427970612Q73546F2Q676C65031F3Q00412Q6C6F772046696C74657220427970612Q7320286E6F207461726765742903153Q004D696E696E674F726546696C746572427970612Q73030F3Q0043726561746550617261677261706803053Q005469746C6503123Q0020416476616E6365642053652Q74696E677303073Q00436F6E74656E74035C3Q0053702Q65642C204865696768742C20616E64206F746865722074756E696E6720736C69646572732061726520696E2074686520504C415945522074616220756E646572204D696E696E6720416476616E6365642073656374696F6E2E03133Q004D696E696E6744656661756C74436F6E66696703103Q004D696E696E675549456C656D656E7473030B3Q0052657365744D696E696E67030A3Q0053746F704D696E696E6703073Q00436C65616E757003063Q00696E73657274030D3Q00556E6C6F6164436C65616E7570030D3Q004D696E696E67204D6F64756C65030C3Q0076342E30204C6F616465642103083Q004475726174696F6E03263Q005B54686520466F7267655D204D696E696E67206D6F64756C652076342E30206C6F6164656421006E062Q00126A012Q00014Q00113Q0001000200126A2Q0100023Q0020540001000100030006B40001001100013Q00046D3Q0011000100126A2Q0100023Q0020540001000100030020540001000100040006B40001001100013Q00046D3Q0011000100126A2Q0100023Q0020540001000100030020540001000100040020540001000100050006402Q01001F0001000100046D3Q001F000100126A2Q0100014Q00110001000100022Q00D5000100013Q000EA80106001A0001000100046D3Q001A000100126A2Q0100073Q001225010200084Q009A2Q01000200012Q00C43Q00013Q00126A2Q0100093Q00205400010001000A0012250102000B4Q009A2Q010002000100046D3Q0002000100126A2Q01000C3Q00200E2Q010001000D00122Q0003000E6Q00010003000200122Q0002000C3Q00202Q00020002000D00122Q0004000F6Q00020004000200122Q0003000C3Q00202Q00030003000D00122Q000500104Q004C0003000500020012930004000C3Q00202Q00040004000D00122Q000600116Q00040006000200202Q00050001001200066B01063Q000100022Q003C3Q00054Q003C3Q00013Q00126A010700023Q00205400070007000300205400080007000400205400080008000500205400090007001300066B010A0001000100022Q003C3Q00094Q003C3Q00073Q00066B010B0002000100012Q003C3Q00074Q003C000C000B4Q002C000D000E4Q0046000F3Q001E00300D000F001400152Q004600105Q001016010F001600102Q004600105Q001016010F001700102Q004600105Q001016010F001800102Q004600105Q001016010F0019001000300D000F001A001B00300D000F001C001D00300D000F001E001F00300D000F0020002100300D000F002200232Q0019001000036Q00113Q000200302Q0011002500264Q00125Q00102Q0011002700124Q00123Q000200302Q0012002500264Q00135Q00102Q0012002700134Q00133Q000200302Q0013002500264Q00145Q00102Q0013002700144Q001000030001001016010F00240010003005000F0028001500302Q000F0029002A00302Q000F002B001D00302Q000F002C002D00302Q000F002E002F00302Q000F0030003100302Q000F0032003300302Q000F0034003500302Q000F0036003700302Q000F003800152Q004600103Q000300300D0010003A003B00300D0010003C003B00300D0010003D003B001016010F00390010003005000F003E003100302Q000F003F003100302Q000F0040003100302Q000F0041003100302Q000F0042004300302Q000F0044004500302Q000F0046001B00302Q000F0047004800302Q000F0049004A00302Q000F004B004C003005000F004D004E00302Q000F004F000B00302Q000F0050005100302Q000F0052005300302Q000F0054005300302Q000F0055005300302Q000F0056005700302Q000F0058005900302Q000F005A001B00302Q000F005B005C003005000F005D001B00302Q000F005E001500302Q000F005F001B00302Q000F0060002A00302Q000F0061006200302Q000F0063006400302Q000F0065006600302Q000F0067006800302Q000F0069004500302Q000F006A001500300D000F006B003B00300D000F006C005100300D000F006D006E2Q004600103Q000900300D00100070001B00300D00100071003100300D00100072007300300D00100074007500300D00100076007700300D0010007800790030790010007A004500302Q0010007B004500302Q0010007C007D00102Q000F006F00104Q00105Q00122Q0011007E6Q0012000F6Q00110002001300044Q00AE000100126A0116007F4Q003C001700154Q00B8001600020002002680001600AD0001008000046D3Q00AD00012Q004600166Q008C01100014001600122Q0016007E6Q001700156Q00160002001800044Q00AA00012Q00A6001B001000142Q003F001B0019001A000677011600A80001000200046D3Q00A8000100046D3Q00AE00012Q003F0010001400150006770111009D0001000200046D3Q009D00012Q004600113Q001B00300500110081002600302Q00110082003B00302Q00110083003B00302Q00110084003B00302Q00110085002600302Q00110086002600302Q00110087002600302Q00110088003B00302Q00110089003B00302Q0011008A003B00300D0011008B003B00300D0011008C00262Q004600125Q0010160111008D001200300D0011008E003B00300D0011008F002600300D00110090002600300D00110091003B2Q004600125Q0010160111009200122Q004600125Q00101601110093001200300D00110094003B00300D00110095002600300D00110096003B00300D00110097003B00300D00110098003B00300D0011009900262Q004600125Q0010160111009A00120030050011009B002600302Q0011009C003B00302Q0011009D001500302Q0011009E003B00302Q0011009F002600302Q001100A0002600302Q001100A1002600302Q001100A2002600302Q001100A3003B00302Q001100A4003B00300D001100A5003B00300D001100A6003B00300D001100A7003B00300D001100A800260030C3001100A9003B4Q00125Q00102Q001100AA001200302Q001100AB003B00302Q001100AC00264Q00128Q00133Q000300302Q001300AD003B00302Q001300AE003B00302Q00130027003B2Q002C0014001C3Q0002BC001D00033Q00126A011E00023Q002054001E001E0003001016011E00AF001000066B011E0004000100012Q003C3Q00044Q0046001F5Q0012250120003B4Q003C0021001E3Q00066B011E0005000100032Q003C3Q001F4Q003C3Q00204Q003C3Q00214Q00FB00225Q00122Q0023003B6Q002400246Q00255Q00122Q0026003B6Q002700276Q00285Q00066B01290006000100012Q003C3Q00043Q00066B012A0007000100012Q003C3Q00044Q003C0024002A3Q00066B012A0008000100042Q003C3Q00284Q003C3Q00224Q003C3Q00234Q003C3Q00243Q00124B012B00B03Q00202Q002B002B00B100122Q002C00B26Q002B0002000200122Q002C00B33Q00122Q002D001F3Q00122Q002E00B43Q00066B012F0009000100012Q003C3Q002B4Q0030002E002F4Q00D6002C3Q000200126A012D00B33Q001225012E001F3Q00126A012F00B43Q00066B0130000A000100012Q003C3Q002B4Q0030002F00304Q00D6002D3Q0002002038002E002B00B52Q009A012E0002000100066B012E000B000100022Q003C3Q002C4Q003C3Q002D3Q00066B012F000C000100022Q003C3Q00014Q003C3Q002E3Q00066B0130000D000100022Q003C3Q00014Q003C3Q002E4Q003C002700303Q00066B0130000E000100032Q003C3Q00254Q003C3Q00264Q003C3Q00273Q00066B0131000F000100012Q003C3Q00013Q0002BC003200103Q0002BC003300113Q0002BC003400124Q004600356Q004600366Q004600375Q0002BC003800133Q00066B01390014000100022Q003C3Q00104Q003C3Q00383Q00066B013A0015000100012Q003C3Q00133Q00066B013B0016000100022Q003C3Q00064Q003C3Q00043Q0002BC003C00174Q002C003D003D3Q001225013E003B4Q0012013F5Q00066B01400018000100042Q003C3Q00284Q003C3Q00374Q003C3Q00224Q003C3Q00353Q00066B01410019000100072Q003C3Q003D4Q003C3Q003E4Q003C3Q00044Q003C3Q003F4Q003C3Q001A4Q003C3Q00404Q003C3Q001B3Q001225014200533Q0012250143003B3Q00066B0144001A000100042Q003C3Q00434Q003C3Q00424Q003C3Q00044Q003C3Q00103Q0020540045000400B600066B0146001B000100022Q003C3Q00454Q003C3Q00043Q00066B0147001C000100072Q003C3Q00104Q003C3Q00464Q003C3Q00394Q003C3Q00114Q003C3Q00024Q003C3Q003B4Q003C3Q000C3Q00066B0148001D000100032Q003C3Q00114Q003C3Q00394Q003C3Q00463Q00066B0149001E000100012Q003C3Q00113Q00066B014A001F000100012Q003C3Q00114Q0046004B5Q00066B014C0020000100012Q003C3Q004B3Q0002BC004D00213Q00066B014E0022000100012Q003C3Q00373Q00066B014F0023000100022Q003C3Q00044Q003C3Q004D3Q00066B01500024000100012Q003C3Q004F3Q00066B01510025000100012Q003C3Q001C3Q00066B01520026000100052Q003C3Q00514Q003C3Q001C4Q003C3Q00104Q003C3Q00124Q003C3Q00503Q00066B01530027000100012Q003C3Q00103Q00066B01540028000100022Q003C3Q00114Q003C3Q00323Q00066B01550029000100022Q003C3Q00114Q003C3Q00323Q00066B0156002A000100032Q003C3Q00114Q003C3Q00324Q003C3Q00103Q00066B0157002B000100062Q003C3Q000D4Q003C3Q00104Q003C3Q00354Q003C3Q00124Q003C3Q000A4Q003C3Q00113Q00066B0158002C000100032Q003C3Q00104Q003C3Q00114Q003C3Q00573Q00066B0159002D000100012Q003C3Q00113Q00066B015A002E000100012Q003C3Q00113Q00066B015B002F000100012Q003C3Q00113Q00066B015C0030000100022Q003C3Q00114Q003C3Q005B3Q00066B015D0031000100012Q003C3Q00113Q00066B015E0032000100012Q003C3Q00103Q00066B015F0033000100052Q003C3Q00124Q003C3Q00114Q003C3Q004D4Q003C3Q005E4Q003C3Q00103Q00066B01600034000100012Q003C3Q00113Q00066B01610035000100042Q003C3Q00104Q003C3Q00604Q003C3Q00114Q003C3Q000A3Q0002BC006200363Q00066B01630037000100022Q003C3Q00104Q003C3Q00623Q00066B01640038000100012Q003C3Q00103Q00066B01650039000100042Q003C3Q004C4Q003C3Q00104Q003C3Q004D4Q003C3Q00533Q00066B0166003A0001000B2Q003C3Q00104Q003C3Q004D4Q003C3Q003B4Q003C3Q000C4Q003C3Q00414Q003C3Q00594Q003C3Q00544Q003C3Q00114Q003C3Q004C4Q003C3Q00654Q003C3Q00393Q00066B0167003B0001000B2Q003C3Q003B4Q003C3Q000C4Q003C3Q00414Q003C3Q00544Q003C3Q00114Q003C3Q004C4Q003C3Q00654Q003C3Q00104Q003C3Q004D4Q003C3Q00394Q003C3Q00593Q0012250168003B3Q0012250169003B4Q002C006A006A3Q00066B016B003C000100072Q003C3Q00114Q003C3Q003B4Q003C3Q000C4Q003C3Q004C4Q003C3Q00394Q003C3Q00104Q003C3Q006B3Q00066B016A003D000100072Q003C3Q00104Q003C3Q00114Q003C3Q003B4Q003C3Q000C4Q003C3Q00394Q003C3Q006B4Q003C3Q00333Q001225016C00623Q001225016D00063Q001225016E003B3Q0002BC006F003E3Q00066B0170003F0001000F2Q003C3Q00194Q003C3Q00034Q003C3Q006E4Q003C3Q00394Q003C3Q00104Q003C3Q00704Q003C3Q006F4Q003C3Q00114Q003C3Q006C4Q003C3Q003B4Q003C3Q000C4Q003C3Q004C4Q003C3Q00684Q003C3Q006D4Q003C3Q004D3Q00066B01710040000100032Q003C3Q00194Q003C3Q00394Q003C3Q006E3Q00066B01720041000100072Q003C3Q00104Q003C3Q00684Q003C3Q00694Q003C3Q00394Q003C3Q00034Q003C3Q003B4Q003C3Q006A3Q00066B01730042000100012Q003C3Q00063Q00066B01740043000100032Q003C3Q00144Q003C3Q00394Q003C3Q00043Q00066B01750044000100052Q003C3Q00144Q003C3Q00744Q003C3Q00104Q003C3Q00044Q003C3Q00393Q00066B01760045000100022Q003C3Q00144Q003C3Q00393Q00066B01770046000100032Q003C3Q003B4Q003C3Q000C4Q003C3Q00153Q00066B017800470001000B2Q003C3Q00774Q003C3Q00764Q003C3Q00164Q003C3Q00174Q003C3Q00184Q003C3Q001D4Q003C3Q001A4Q003C3Q001B4Q003C3Q003F4Q003C3Q00714Q003C3Q00393Q00066B01790048000100082Q003C3Q00104Q003C3Q00114Q003C3Q00694Q003C3Q003C4Q003C3Q00394Q003C3Q00764Q003C3Q00744Q003C3Q00163Q00066B017A0049000100012Q003C3Q00103Q00066B017B004A000100102Q003C3Q00754Q003C3Q00394Q003C3Q007A4Q003C3Q00444Q003C3Q00104Q003C3Q00114Q003C3Q004D4Q003C3Q005E4Q003C3Q005F4Q003C3Q00324Q003C3Q004E4Q003C3Q00614Q003C3Q00604Q003C3Q000A4Q003C3Q00724Q003C3Q00153Q00066B017C004B0001000B2Q003C3Q00174Q003C3Q00184Q003C3Q00714Q003C3Q00774Q003C3Q00764Q003C3Q00154Q003C3Q004A4Q003C3Q00484Q003C3Q00114Q003C3Q00694Q003C3Q00393Q00066B017D004C000100212Q003C3Q001D4Q003C3Q00174Q003C3Q00114Q003C3Q00394Q003C3Q00474Q003C3Q00494Q003C3Q00744Q003C3Q00704Q003C3Q00184Q003C3Q00024Q003C3Q00104Q003C3Q003B4Q003C3Q00734Q003C3Q00794Q003C3Q00554Q003C3Q00564Q003C3Q000C4Q003C3Q00774Q003C3Q00334Q003C3Q004D4Q003C3Q00674Q003C3Q005B4Q003C3Q005D4Q003C3Q00694Q003C3Q000F4Q003C3Q005A4Q003C3Q00664Q003C3Q00654Q003C3Q00414Q003C3Q005F4Q003C3Q004C4Q003C3Q00584Q003C3Q007B3Q00066B017E004D000100062Q003C3Q000A4Q003C3Q00104Q003C3Q007D4Q003C3Q00524Q003C3Q007C4Q003C3Q00513Q002038007F000800B7001225018100B84Q007D007F00810001002038007F000800BA2Q004600813Q000400300D008100BB00BC00300D008100BD001500300D008100BE00BF00066B0182004E000100012Q003C3Q007E3Q001016018100C000822Q0027017F0081000200102Q001200B9007F00202Q007F000800BA4Q00813Q000400302Q008100BB00C200300D008100BD001B00300D008100BE00C300066B0182004F000100012Q003C3Q00103Q0010CB008100C000824Q007F0081000200102Q001200C1007F00202Q007F000800C54Q00813Q000700302Q008100BB00C64Q008200023Q00122Q0083000B3Q00122Q008400686Q008200020001001016018100C70082003008018100C8000B00302Q008100C900CA00202Q00820010006F00202Q00820082007C00102Q008100BD008200302Q008100BE00CB00066B01820050000100012Q003C3Q00103Q0010CB008100C000824Q007F0081000200102Q001200C4007F00202Q007F000800C54Q00813Q000700302Q008100BB00CD4Q008200023Q00122Q0083001F3Q00122Q008400776Q008200020001001016018100C70082003008018100C8000B00302Q008100C900CE00202Q00820010006F00202Q00820082007B00102Q008100BD008200302Q008100BE00CF00066B01820051000100012Q003C3Q00103Q001016018100C000822Q0027017F0081000200102Q001200CC007F00202Q007F000800D04Q00813Q000200302Q008100BB00D100066B01820052000100022Q003C3Q00794Q003C3Q000A3Q00102E008100C000824Q007F0081000100202Q007F000800D04Q00813Q000200302Q008100BB00D200066B01820053000100032Q003C3Q00114Q003C3Q003C4Q003C3Q000A3Q001016018100C000822Q007D007F00810001002038007F000800B7001225018100D34Q007D007F0081000100066B010D0054000100052Q003C3Q00284Q003C3Q00354Q003C3Q00104Q003C3Q002A4Q003C3Q00293Q00066B010E0055000100032Q003C3Q00364Q003C3Q00304Q003C3Q00124Q003C007F001E4Q0011007F000100022Q003C001F007F3Q002054007F001000162Q002E017F007F3Q002680007F00E40201003B00046D3Q00E402012Q003C007F000D4Q00C8008000016Q007F000200014Q007F000E6Q008000016Q007F0002000100122Q007F00D43Q00122Q008000D56Q008100353Q00122Q008200D66Q0080008000822Q009A017F00020001001294007F00D43Q00122Q008000D76Q008100363Q00122Q008200D86Q0080008000824Q007F0002000100044Q00F302012Q003C007F000D4Q0097018000016Q007F000200014Q007F000E6Q008000016Q007F0002000100122Q007F00D43Q00122Q008000D93Q00202Q0081001000164Q008100813Q00122Q008200DA4Q002E018300353Q001225018400D64Q007A0080008000842Q009A017F00020001002038007F000800DC2Q00A101813Q000600302Q008100BB00DD00102Q008100DE001F00202Q00820010001600102Q008100DF008200302Q008100E0001B00302Q008100BE00E100066B01820056000100062Q003C3Q00114Q003C3Q00104Q003C3Q000D4Q003C3Q00124Q003C3Q00354Q003C3Q00393Q0010B0008100C000824Q007F0081000200102Q001200DB007F00202Q007F000800E300122Q008100E43Q00202Q0082001000164Q008200823Q000E2Q003B00120301008200046D3Q0012030100126A018200803Q0020540082008200E5002054008300100016001225018400E64Q004C008200840002000640018200130301000100046D3Q00130301001225018200E74Q007A0081008100822Q0027017F0081000200102Q001200E2007F00202Q007F000800D04Q00813Q000200302Q008100BB00E800066B01820057000100052Q003C3Q003A4Q003C3Q001F4Q003C3Q001E4Q003C3Q00124Q003C3Q000A3Q00102E008100C000824Q007F0081000100202Q007F000800D04Q00813Q000200302Q008100BB00E900066B018200580001000A2Q003C3Q00104Q003C3Q00124Q003C3Q00114Q003C3Q000D4Q003C3Q00354Q003C3Q000E4Q003C3Q00364Q003C3Q005F4Q003C3Q000A4Q003C3Q00393Q00102E008100C000824Q007F0081000100202Q007F000800D04Q00813Q000200302Q008100BB00EA00066B01820059000100022Q003C3Q003A4Q003C3Q00573Q00102E008100C000824Q007F0081000100202Q007F000800D04Q00813Q000200302Q008100BB00EB00066B0182005A000100062Q003C3Q003A4Q003C3Q000E4Q003C3Q00364Q003C3Q00104Q003C3Q00124Q003C3Q000A3Q00102E008100C000824Q007F0081000100202Q007F000800D04Q00813Q000200302Q008100BB00EC00066B0182005B000100052Q003C3Q00104Q003C3Q002A4Q003C3Q00354Q003C3Q00304Q003C3Q000A3Q00102E008100C000824Q007F0081000100202Q007F000800DC4Q00813Q000500302Q008100BB00EE2Q0046008200023Q001225018300EF3Q0012250184002F4Q00CD008200020001001016018100DE00822Q0046008200013Q00205400830010002E2Q00CD008200010001001016018100DF008200300D008100BE00F000066B0182005C000100012Q003C3Q00103Q001081008100C000824Q007F0081000200102Q001200ED007F00202Q007F000800DC4Q00813Q000500302Q008100BB00F24Q008200033Q00122Q008300F33Q00122Q008400643Q00122Q008500F44Q00CD008200030001001016018100DE00822Q0046008200013Q0020540083001000632Q00CD008200010001001016018100DF008200300D008100BE00F500066B0182005D000100042Q003C3Q00104Q003C3Q00484Q003C3Q00474Q003C3Q00393Q001016018100C000822Q004C007F00810002001016011200F1007F002038007F000800B7001225018100F64Q007D007F00810001002038007F000800C52Q004600813Q000700300D008100BB00F82Q0046008200023Q001225018300F93Q001225018400FA4Q00CD008200020001001016018100C700820030E3008100C800FB00302Q008100C900CA00202Q00820010002B00102Q008100BD008200302Q008100BE00FC00066B0182005E000100012Q003C3Q00103Q0010CB008100C000824Q007F0081000200102Q001200F7007F00202Q007F000800C54Q00813Q000700302Q008100BB00FE4Q008200023Q00122Q0083003B3Q00122Q008400FF6Q008200020001001016018100C700820030E3008100C800FB00302Q008100C900CA00202Q00820010006D00102Q008100BD008200302Q008100BE2Q0001066B0182005F000100012Q003C3Q00103Q001016018100C000822Q004C007F00810002001016011200FD007F001225017F002Q012Q0020380080000800C52Q004600823Q000700122501830002012Q001016018200BB00832Q0046008300023Q00122501840003012Q001225018500684Q00CD008300020001001016018200C700830012250183001D3Q001016018200C8008300300D008200C900CE00205400830010006B001016018200BD008300122501830004012Q001016018200BE008300066B01830060000100012Q003C3Q00103Q00107C018200C000834Q0080008200024Q0012007F008000122Q007F0005012Q00202Q0080000800C54Q00823Q000700122Q00830006012Q00102Q008200BB00834Q008300023Q00122Q0084003B3Q001225018500454Q00CD008300020001001016018200C700830012250183001D3Q001016018200C8008300300D008200C900CE00205400830010006C001016018200BD008300122501830007012Q001016018200BE008300066B01830061000100012Q003C3Q00103Q001050008200C000834Q0080008200024Q0012007F008000202Q007F000800B700122Q00810008015Q007F0081000100122Q007F0009012Q00202Q0080000800DC4Q00823Q000600122Q0083000A012Q001016018200BB00832Q002E018300353Q0012250184003B3Q0006A3018400D90301008300046D3Q00D90301000639018300DC0301003500046D3Q00DC03012Q0046008300013Q0012250184000B013Q00CD008300010001001016018200DE00832Q002201835Q00102Q008200DF00834Q008300013Q00102Q008200E0008300122Q0083000C012Q00102Q008200BE008300066B01830062000100052Q003C3Q00104Q003C3Q00354Q003C3Q00114Q003C3Q00124Q003C3Q00503Q001062018200C000834Q0080008200024Q0012007F008000122Q007F000D012Q00202Q0080000800E300122Q008200E43Q00202Q0083001000174Q008300833Q00122Q0084003B3Q00062Q008400FB0301008300046D3Q00FB030100126A018300803Q0020540083008300E5002054008400100017001225018500E64Q004C008300850002000640018300FC0301000100046D3Q00FC03010012250183000E013Q007A0082008200832Q004C0080008200022Q003F0012007F0080001225017F000F012Q0020380080000800E300122501820010013Q004C0080008200022Q003F0012007F0080002038007F000800B700122501810011013Q007D007F00810001001225017F0012012Q0020380080000800BA2Q004600823Q000400122501830013012Q001016018200BB00832Q0012018300013Q001016018200BD008300122501830014012Q001016018200BE008300066B01830063000100012Q003C3Q00103Q001016018200C000832Q004C0080008200022Q003F0012007F0080001225017F0015012Q00205A0180000800E300122Q00820016015Q0080008200024Q0012007F008000202Q007F000800D04Q00813Q000200122Q00820017012Q00102Q008100BB008200066B01820064000100032Q003C3Q00104Q003C3Q000A4Q003C3Q00123Q001016018100C000822Q007D007F00810001001225017F0018012Q0020380080000800C52Q004600823Q000600122501830019012Q001016018200BB00832Q0046008300023Q001225018400F93Q0012250185001F4Q00CD008300020001001016018200C70083001297008300F93Q00102Q008200C8008300202Q00830010001C00102Q008200BD008300122Q0083001A012Q00102Q008200BE008300066B01830065000100012Q003C3Q00103Q00107C018200C000834Q0080008200024Q0012007F008000122Q007F001B012Q00202Q0080000800C54Q00823Q000600122Q0083001C012Q00102Q008200BB00834Q008300023Q00122Q0084003B3Q001225018500454Q00CD008300020001001016018200C700830012970083001D3Q00102Q008200C8008300202Q00830010001E00102Q008200BD008300122Q0083001D012Q00102Q008200BE008300066B01830066000100012Q003C3Q00103Q00107C018200C000834Q0080008200024Q0012007F008000122Q007F001E012Q00202Q0080000800C54Q00823Q000600122Q0083001F012Q00102Q008200BB00834Q008300023Q00122Q0084003B3Q001225018500684Q00CD008300020001001016018200C700830012970083000B3Q00102Q008200C8008300202Q00830010002200102Q008200BD008300122Q00830020012Q00102Q008200BE008300066B01830067000100012Q003C3Q00103Q00107C018200C000834Q0080008200024Q0012007F008000122Q007F0021012Q00202Q0080000800C54Q00823Q000600122Q00830022012Q00102Q008200BB00834Q008300023Q00122Q0084003B3Q001225018500484Q00CD008300020001001016018200C700830012970083001F3Q00102Q008200C8008300202Q00830010002000102Q008200BD008300122Q00830023012Q00102Q008200BE008300066B01830068000100012Q003C3Q00103Q001016018200C000832Q00880080008200024Q0012007F008000202Q007F000800D04Q00813Q000200122Q00820024012Q00102Q008100BB008200066B01820069000100042Q003C3Q00104Q003C3Q00124Q003C3Q00114Q003C3Q000A3Q001016018100C000822Q007D007F00810001001225017F0025012Q0020380080000800DC2Q004600823Q000600122501830026012Q001016018200BB00832Q002E018300363Q0012250184003B3Q0006A30184008E0401008300046D3Q008E0401000639018300910401003600046D3Q009104012Q0046008300013Q00122501840027013Q00CD008300010001001016018200DE00832Q002201835Q00102Q008200DF00834Q008300013Q00102Q008200E0008300122Q00830028012Q00102Q008200BE008300066B0183006A000100052Q003C3Q00104Q003C3Q00364Q003C3Q00114Q003C3Q00124Q003C3Q005F3Q001062018200C000834Q0080008200024Q0012007F008000122Q007F0029012Q00202Q0080000800E300122Q0082002A012Q00202Q0083001000184Q008300833Q00122Q0084003B3Q00062Q008400B00401008300046D3Q00B0040100126A018300803Q0020540083008300E5002054008400100018001225018500E64Q004C008300850002000640018300B10401000100046D3Q00B104010012250183000E013Q007A0082008200832Q00880080008200024Q0012007F008000202Q007F000800D04Q00813Q000200122Q0082002B012Q00102Q008100BB008200066B0182006B000100052Q003C3Q00104Q003C3Q00114Q003C3Q00124Q003C3Q005F4Q003C3Q000A3Q001090008100C000824Q007F0081000100122Q007F002C012Q00202Q0080000800BA4Q00823Q000400122Q0083002D012Q00102Q008200BB008300202Q00830010005F00102Q008200BD008300122Q0083002E012Q001016018200BE008300066B0183006C000100032Q003C3Q00104Q003C3Q00114Q003C3Q005F3Q001085018200C000834Q0080008200024Q0012007F008000122Q007F002F012Q00202Q0080000800E300122Q00820030015Q0080008200024Q0012007F008000122Q007F0031012Q00202Q0080000800BA2Q004600823Q000400129700830032012Q00102Q008200BB008300202Q00830010006A00102Q008200BD008300122Q00830033012Q00102Q008200BE008300066B0183006D000100012Q003C3Q00103Q00107E018200C000834Q0080008200024Q0012007F008000202Q007F000800B700122Q00810034015Q007F0081000100066B017F006E000100012Q003C3Q00353Q00066B0180006F000100012Q003C3Q00363Q00066B01810070000100022Q003C3Q00124Q003C3Q00103Q00066B01820071000100052Q003C3Q00644Q003C3Q00634Q003C3Q00114Q003C3Q00814Q003C3Q005F3Q00066B01830072000100052Q003C3Q00644Q003C3Q00634Q003C3Q00114Q003C3Q00814Q003C3Q005F3Q00121A01840035012Q00202Q0085000800DC4Q00873Q000600122Q00880036012Q00102Q008700BB00884Q0088007F6Q00880001000200102Q008700DE00884Q008800013Q00122Q00890037013Q00CD008800010001001016018700DF00882Q00A401885Q00102Q008700E0008800122Q00880038012Q00102Q008700BE00884Q008800823Q00122Q0089001F6Q00880002000200102Q008700C000884Q0085008700024Q00120084008500121A01840039012Q00202Q0085000800DC4Q00873Q000600122Q0088003A012Q00102Q008700BB00884Q008800806Q00880001000200102Q008700DE00884Q008800013Q00122Q00890037013Q00CD008800010001001016018700DF00882Q00A4018800013Q00102Q008700E0008800122Q0088003B012Q00102Q008700BE00884Q008800833Q00122Q0089001F6Q00880002000200102Q008700C000884Q0085008700024Q0012008400850012250184003C012Q0020870085000800E300122Q0087003D015Q0085008700024Q00120084008500122Q0084003E012Q00202Q0085000800DC4Q00873Q000600122Q0088003F012Q00102Q008700BB00884Q0088007F4Q0011008800010002001016018700DE00882Q0046008800013Q00122501890037013Q00CD008800010001001016018700DF00882Q00A401885Q00102Q008700E0008800122Q00880040012Q00102Q008700BE00884Q008800823Q00122Q00890041015Q00880002000200102Q008700C000884Q0085008700024Q00120084008500121A01840042012Q00202Q0085000800DC4Q00873Q000600122Q00880043012Q00102Q008700BB00884Q008800806Q00880001000200102Q008700DE00884Q008800013Q00122Q00890037013Q00CD008800010001001016018700DF00882Q00A4018800013Q00102Q008700E0008800122Q00880044012Q00102Q008700BE00884Q008800833Q00122Q00890041015Q00880002000200102Q008700C000884Q0085008700024Q00120084008500122501840045012Q0020870085000800E300122Q0087003D015Q0085008700024Q00120084008500122Q00840046012Q00202Q0085000800DC4Q00873Q000600122Q00880047012Q00102Q008700BB00884Q0088007F4Q0011008800010002001016018700DE00882Q0046008800013Q00122501890037013Q00CD008800010001001016018700DF00882Q00A401885Q00102Q008700E0008800122Q00880048012Q00102Q008700BE00884Q008800823Q00122Q0089007D6Q00880002000200102Q008700C000884Q0085008700024Q00120084008500121A01840049012Q00202Q0085000800DC4Q00873Q000600122Q0088004A012Q00102Q008700BB00884Q008800806Q00880001000200102Q008700DE00884Q008800013Q00122Q00890037013Q00CD008800010001001016018700DF00882Q00A4018800013Q00102Q008700E0008800122Q0088004B012Q00102Q008700BE00884Q008800833Q00122Q0089007D6Q00880002000200102Q008700C000884Q0085008700024Q0012008400850012250184004C012Q00205A0185000800E300122Q0087003D015Q0085008700024Q00120084008500202Q0084000800D04Q00863Q000200122Q0087004D012Q00102Q008600BB008700066B01870073000100062Q003C3Q00634Q003C3Q00124Q003C3Q00114Q003C3Q00814Q003C3Q005F4Q003C3Q000A3Q001016018600C000872Q007D0084008600010020380084000800D02Q004600863Q00020012250187004E012Q001016018600BB008700066B01870074000100082Q003C3Q000E4Q003C3Q00644Q003C3Q00634Q003C3Q00124Q003C3Q000A4Q003C3Q00114Q003C3Q00814Q003C3Q005F3Q001016018600C000872Q007D0084008600012Q004600843Q00050012250185004F013Q0046008600063Q00122501870050012Q0012AF00880051012Q00122Q00890052012Q00122Q008A0053012Q00122Q008B0054012Q00122Q008C0055015Q0086000600012Q003F00840085008600122501850056013Q0046008600053Q0012AF00870050012Q00122Q00880051012Q00122Q00890052012Q00122Q008A0053012Q00122Q008B0054015Q0086000500012Q003F00840085008600120300850057015Q008600033Q00122Q00870058012Q00122Q00880059012Q00122Q0089005A015Q0086000300012Q003F0084008500860012250185005B013Q0046008600043Q0012720087005C012Q00122Q0088005D012Q00122Q0089005E012Q00122Q008A005F015Q0086000400012Q003F00840085008600122501850060013Q004600866Q003F00840085008600122501850061012Q0020380086000800DC2Q004600883Q000600122501890062012Q001016018800BB00892Q0046008900053Q0012AF008A004F012Q00122Q008B0056012Q00122Q008C0057012Q00122Q008D005B012Q00122Q008E0060015Q008900050001001016018800DE00892Q002201895Q00102Q008800DF00894Q00895Q00102Q008800E0008900122Q00890063012Q00102Q008800BE008900066B01890075000100082Q003C3Q00844Q003C3Q000E4Q003C3Q00364Q003C3Q00104Q003C3Q000A4Q003C3Q00124Q003C3Q00114Q003C3Q005F3Q001075008800C000894Q0086008800024Q00120085008600122Q00850064012Q00202Q0086000800BA4Q00883Q000400122Q00890065012Q00102Q008800BB008900202Q00890010005A00102Q008800BD008900122501890066012Q001016018800BE008900066B01890076000100012Q003C3Q00103Q001075008800C000894Q0086008800024Q00120085008600122Q00850067012Q00202Q0086000800BA4Q00883Q000400122Q00890068012Q00102Q008800BB008900202Q00890010005D00102Q008800BD008900122501890069012Q001016018800BE008900066B01890077000100012Q003C3Q00103Q001075008800C000894Q0086008800024Q00120085008600122Q0085006A012Q00202Q0086000800BA4Q00883Q000400122Q0089006B012Q00102Q008800BB008900202Q00890010005E00102Q008800BD00890012250189006C012Q001016018800BE008900066B01890078000100022Q003C3Q00104Q003C3Q00113Q0010F8008800C000894Q0086008800024Q00120085008600122Q0087006D015Q0085000800874Q00873Q000200122Q0088006E012Q00122Q0089006F015Q00870088008900122Q00880070012Q00122501890071013Q003F0087008800892Q007D00850087000100126A018500023Q002054008500850003001016018500AF001000126A018500023Q00205400850085000300122501860072013Q003F00850086000F00126A018500023Q00205400850085000300122501860073013Q003F00850086001200126A018500023Q00205400850085000300122501860074012Q00066B01870079000100062Q003C3Q00104Q003C3Q007C4Q003C3Q00124Q003C3Q000F4Q003C3Q00114Q003C3Q00164Q003F00850086008700126A018500023Q00205400850085000300122501860075012Q00066B0187007A000100062Q003C3Q00104Q003C3Q001D4Q003C3Q00174Q003C3Q007C4Q003C3Q00514Q003C3Q00124Q006E00850086008700122Q00850076012Q00122Q00860076015Q00860007008600062Q008600490601000100046D3Q004906012Q004600866Q003F0007008500860012DC008500803Q00122Q00860077015Q00850085008600122Q00860076015Q0086000700864Q008700786Q00850087000100122Q0085007F3Q00122Q00860078015Q0086000700862Q00B80085000200020026800085005E0601008000046D3Q005E060100126A018500803Q00120301860077015Q00850085008600122Q00860078015Q0086000700864Q008700786Q0085008700012Q003C0085000A4Q004600863Q00030012250187006E012Q00122501880079013Q003F00860087008800122501870070012Q0012250188007A013Q003F0086008700880012250187007B012Q00122501880041013Q003F0086008700882Q009A01850002000100126A018500D43Q0012250186007C013Q009A0185000200012Q00C43Q00013Q007B3Q00013Q00030B3Q004C6F63616C506C6179657200094Q00A47Q000640012Q00060001000100046D3Q000600012Q00A43Q00013Q0020545Q00012Q00D78Q00A48Q003A3Q00024Q00C43Q00017Q00023Q0003083Q005261796669656C6403063Q004E6F7469667901114Q00A400015Q0006402Q0100080001000100046D3Q000800012Q00A4000100013Q0006B40001000800013Q00046D3Q000800012Q00A4000100013Q0020540001000100010006B40001001000013Q00046D3Q001000010020540002000100020006B40002001000013Q00046D3Q001000010020380002000100022Q003C00046Q007D0002000400012Q00C43Q00017Q00063Q0003053Q005574696C7303073Q00476574522Q6F7403043Q007479706503083Q0066756E6374696F6E030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727401184Q00A400015Q0006B40001000500013Q00046D3Q000500012Q00A400015Q0020540001000100010006FE000200080001000100046D3Q0008000100205400020001000200126A010300034Q003C000400024Q00B8000300020002002680000300110001000400046D3Q001100012Q003C000300024Q003C00046Q00FF000300044Q002D00035Q0006FE0003001600013Q00046D3Q0016000100203800033Q0005001225010500064Q004C0003000500022Q003A000300024Q00C43Q00017Q00023Q0003093Q00436F2Q6E6563746564010001093Q0006FE0001000700013Q00046D3Q0007000100205400013Q0001002680000100060001000200046D3Q000600012Q00132Q016Q00122Q0100014Q003A000100024Q00C43Q00017Q00143Q00030B3Q005B412Q6C2041726561735D030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007072696E74032A3Q005B466F726765204D696E696E675D2Q20576F726B73706163652E526F636B73206E6F7420666F756E642103103Q00284E6F20417265617320466F756E642903053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C03053Q007461626C6503063Q00696E7365727403043Q004E616D6503043Q00736F727403063Q00697061697273028Q0003063Q00737472696E6703063Q00666F726D617403383Q005B466F726765204D696E696E675D2Q20466F756E64202564206D696E696E6720617265617320696E20576F726B73706163652E526F636B7300464Q00463Q00013Q0012252Q0100014Q00CD3Q000100012Q00A400015Q002038000100010002001225010300034Q004C0001000300020006402Q0100100001000100046D3Q0010000100126A010200043Q001225010300054Q009A0102000200012Q0046000200013Q001225010300064Q00CD0002000100012Q003A000200024Q004600025Q0012A7000300073Q00202Q0004000100084Q000400056Q00033Q000500044Q00250001002038000800070009001225010A000A4Q004C0008000A0002000640010800200001000100046D3Q00200001002038000800070009001225010A000B4Q004C0008000A00020006B40008002500013Q00046D3Q0025000100126A0108000C3Q00205400080008000D2Q003C000900023Q002054000A0007000E2Q007D0008000A0001000677010300160001000200046D3Q0016000100126A0103000C3Q00207F00030003000F4Q000400026Q00030002000100122Q000300106Q000400026Q00030002000500044Q0034000100126A0108000C3Q00205400080008000D2Q003C00096Q003C000A00074Q007D0008000A00010006770103002F0001000200046D3Q002F00012Q002E010300023Q0026800003003D0001001100046D3Q003D00012Q0046000300013Q001225010400064Q00CD0003000100012Q003A000300023Q00126A010300043Q00122C010400123Q00202Q00040004001300122Q000500146Q000600026Q000400066Q00033Q00016Q00028Q00017Q00033Q0003043Q007469636B028Q00026Q00F03F01153Q00126A2Q0100014Q0011000100010002000640012Q000E0001000100046D3Q000E00012Q00A400026Q002E010200023Q000EA80102000E0001000200046D3Q000E00012Q00A4000200014Q00D50002000100020026320102000E0001000300046D3Q000E00012Q00A400026Q003A000200024Q00A4000200024Q00840002000100024Q00028Q000100016Q00028Q000200028Q00017Q000B3Q00030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03043Q004E616D652Q0103053Q007461626C6503063Q00696E7365727403043Q00736F727401354Q00D100018Q00025Q00202Q00020002000100122Q000400026Q00020004000200062Q000200090001000100046D3Q000900012Q004600036Q003A000300023Q0020380003000200012Q003C00056Q004C0003000500020006B40003002300013Q00046D3Q0023000100126A010400033Q0020380005000300042Q0030000500064Q002300043Q000600046D3Q0021000100126A010900033Q002038000A000800042Q0030000A000B4Q002300093Q000B00046D3Q001F0001002038000E000D0005001225011000064Q004C000E001000020006B4000E001F00013Q00046D3Q001F0001002054000E000D00070020090001000E0008000677010900180001000200046D3Q00180001000677010400130001000200046D3Q001300012Q004600045Q00126A010500034Q003C000600014Q006400050002000700046D3Q002D000100126A010900093Q00205400090009000A2Q003C000A00044Q003C000B00084Q007D0009000B0001000677010500280001000100046D3Q0028000100126A010500093Q0020B500050005000B4Q000600046Q0005000200014Q000400028Q00017Q000C3Q00030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C03043Q004E616D652Q0103053Q007461626C6503063Q00696E7365727403043Q00736F727400414Q00D19Q0000015Q00202Q00010001000100122Q000300026Q00010003000200062Q000100090001000100046D3Q000900012Q004600026Q003A000200023Q00126A010200033Q0020380003000100042Q0030000300044Q002300023Q000400046D3Q002D0001002038000700060005001225010900064Q004C000700090002000640010700180001000100046D3Q00180001002038000700060005001225010900074Q004C0007000900020006B40007002D00013Q00046D3Q002D000100126A010700033Q0020380008000600042Q0030000800094Q002300073Q000900046D3Q002B000100126A010C00033Q002038000D000B00042Q0030000D000E4Q0023000C3Q000E00046D3Q00290001002038001100100005001225011300074Q004C0011001300020006B40011002900013Q00046D3Q002900010020540011001000080020093Q00110009000677010C00220001000200046D3Q002200010006770107001D0001000200046D3Q001D00010006770102000E0001000200046D3Q000E00012Q004600025Q00126A010300034Q003C00046Q006400030002000500046D3Q0039000100126A0107000A3Q00205400070007000B2Q003C000800024Q003C000900064Q007D000700090001000677010300340001000100046D3Q0034000100126A0103000A3Q0020B500030003000C4Q000400026Q0003000200014Q000200028Q00017Q00033Q0003043Q007469636B028Q00026Q00F03F011F3Q00126A2Q0100014Q00110001000100022Q00A400025Q0006B40002000700013Q00046D3Q000700012Q004600026Q00D7000200013Q000640012Q00160001000100046D3Q001600012Q00A400025Q000640010200160001000100046D3Q001600012Q00A4000200014Q002E010200023Q000EA8010200160001000200046D3Q001600012Q00A4000200024Q00D5000200010002002632010200160001000300046D3Q001600012Q00A4000200014Q003A000200024Q00A4000200034Q00370002000100024Q000200016Q000100026Q00028Q00028Q000200016Q000200028Q00017Q00023Q002Q033Q0049734103063Q0055494261736500064Q0079016Q00206Q000100122Q000200028Q00029Q008Q00017Q00023Q002Q033Q00497341030B3Q005549436F6D706F6E656E7400064Q0079016Q00206Q000100122Q000200028Q00029Q008Q00017Q00043Q0003043Q004E616D652Q033Q0049734103063Q00554942617365030B3Q005549436F6D706F6E656E7402233Q000640012Q00040001000100046D3Q000400012Q0012010200014Q003A000200023Q0006B40001000C00013Q00046D3Q000C000100205400023Q00012Q00A60002000100020006B40002000C00013Q00046D3Q000C00012Q0012010200014Q003A000200024Q00A400025Q0006B40002001600013Q00046D3Q0016000100203800023Q0002001225010400034Q004C0002000400020006B40002001600013Q00046D3Q001600012Q0012010200014Q003A000200024Q00A4000200013Q0006B40002002000013Q00046D3Q0020000100203800023Q0002001225010400044Q004C0002000400020006B40002002000013Q00046D3Q002000012Q0012010200014Q003A000200024Q001201026Q003A000200024Q00C43Q00017Q001E3Q00030B3Q004C6F63616C506C6179657203053Q007063612Q6C030C3Q005549477269644C61796F75742Q01030C3Q0055494C6973744C61796F757403093Q00554950612Q64696E6703173Q005549417370656374526174696F436F6E73747261696E7403073Q0055495363616C6503083Q0055495374726F6B6503083Q005549436F726E657203073Q005468655065616B030D3Q00546865205065616B204C69737403043Q005065616B030E3Q0046696E6446697273744368696C6403053Q007461626C6503043Q00736F727403053Q007072696E7403203Q005B466F726765204D696E696E675D204765744F726573466F7249736C616E642803093Q00293A20466F756E642003113Q00206F72657320766961206D612Q70696E6703053Q00204C69737403043Q006773756203063Q0049736C616E64034Q0003043Q004361766503053Q0053746172742Q033Q0052656403063Q0069706169727303103Q00206F72657320286D6174636865643A2003013Q002901714Q004600016Q00A400025Q00205400020002000100126A010300023Q00066B01043Q000100012Q003C3Q00024Q00640003000200040006B40003000B00013Q00046D3Q000B00010006400104000D0001000100046D3Q000D00012Q004600056Q003A000500024Q004600053Q000700300D00050003000400300D00050005000400300D00050006000400300D00050007000400300D00050008000400300D00050009000400300D0005000A000400066B01060001000100032Q00A43Q00014Q003C3Q00054Q003C3Q00014Q003801073Q000200302Q0007000B000C00302Q0007000D000C4Q000800073Q00062Q0008003400013Q00046D3Q0034000100203800090004000E2Q003C000B00084Q004C0009000B00020006B40009003400013Q00046D3Q003400012Q003C000A00064Q004A010B00096Q000A0002000100122Q000A000F3Q00202Q000A000A00104Q000B00016Q000A0002000100122Q000A00113Q00122Q000B00126Q000C5Q00122Q000D00134Q002E010E00013Q001225010F00144Q007A000B000B000F2Q009A010A000200012Q003A000100024Q0046000900064Q003C000A5Q001225010B00154Q007A000A000A000B2Q003C000B5Q002038000C3Q0016001289010E00173Q00122Q000F00186Q000C000F000200122Q000D00156Q000C000C000D00202Q000D3Q001600122Q000F00193Q00122Q001000186Q000D0010000200122Q000E00154Q007A000D000D000E002038000E3Q00160012890110001A3Q00122Q001100186Q000E0011000200122Q000F00156Q000E000E000F00202Q000F3Q001600122Q0011001B3Q00122Q001200186Q000F0012000200122Q001000154Q007A000F000F00102Q00CD00090006000100126A010A001C4Q003C000B00094Q0064000A0002000C00046D3Q00690001002038000F0004000E2Q003C0011000E4Q004C000F001100020006B4000F006900013Q00046D3Q006900012Q003C001000064Q00B90011000F6Q00100002000100122Q001000113Q00122Q001100126Q00125Q00122Q001300136Q001400013Q00122Q0015001D6Q0016000E3Q00122Q0017001E6Q0011001100174Q00100002000100044Q006B0001000677010A00560001000200046D3Q0056000100126A010A000F3Q0020B5000A000A00104Q000B00016Q000A000200014Q000100028Q00013Q00023Q00073Q0003093Q00506C6179657247756903043Q004D656E7503053Q004672616D6503053Q004D656E757303053Q00496E64657803053Q00506167657303043Q004F726573000B4Q0036016Q00206Q000100206Q000200206Q000300206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00053Q0003053Q007061697273030B3Q004765744368696C6472656E03053Q007461626C6503063Q00696E7365727403043Q004E616D6501133Q0012A7000100013Q00202Q00023Q00024Q000200036Q00013Q000300044Q001000012Q00A400066Q003C000700054Q00A4000800014Q004C000600080002000640010600100001000100046D3Q0010000100126A010600033Q0020540006000600042Q00A4000700023Q0020540008000500052Q007D0006000800010006772Q0100050001000200046D3Q000500012Q00C43Q00017Q00163Q00030B3Q004C6F63616C506C6179657203053Q007063612Q6C030C3Q005549477269644C61796F75742Q01030C3Q0055494C6973744C61796F757403093Q00554950612Q64696E6703173Q005549417370656374526174696F436F6E73747261696E7403073Q0055495363616C6503083Q0055495374726F6B6503083Q005549436F726E657203053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D652Q033Q00737562026Q0014C003053Q00204C69737403053Q007461626C6503063Q00696E7365727403043Q00736F727403053Q007072696E7403253Q005B466F726765204D696E696E675D20476574412Q6C4F726554797065733A20466F756E6420031B3Q0020756E69717565206F7265732066726F6D20506C6179657247756900474Q00468Q004600016Q00A400025Q00205400020002000100126A010300023Q00066B01043Q000100012Q003C3Q00024Q00640003000200040006B40003000C00013Q00046D3Q000C00010006400104000E0001000100046D3Q000E00012Q004600056Q003A000500024Q004600053Q000700302Q00050003000400302Q00050005000400302Q00050006000400302Q00050007000400302Q00050008000400302Q00050009000400302Q0005000A000400122Q0006000B3Q00202Q00070004000C4Q000700086Q00063Q000800044Q00390001002054000B000A000D002038000B000B000E001225010D000F4Q004C000B000D0002002680000B00390001001000046D3Q0039000100126A010B000B3Q002038000C000A000C2Q0030000C000D4Q0023000B3Q000D00046D3Q003700012Q00A4001000014Q003C0011000F4Q003C001200054Q004C001000120002000640011000370001000100046D3Q003700010020540010000F000D2Q00A6001000010010000640011000370001000100046D3Q003700010020540010000F000D0020A92Q010010000400122Q001000113Q00202Q0010001000124Q00115Q00202Q0012000F000D4Q001000120001000677010B00260001000200046D3Q002600010006770106001B0001000200046D3Q001B000100126A010600113Q0020540006000600132Q003C00076Q009A01060002000100126A010600143Q001225010700154Q002E01085Q001225010900164Q007A0007000700092Q009A0106000200012Q003A3Q00024Q00C43Q00013Q00013Q00073Q0003093Q00506C6179657247756903043Q004D656E7503053Q004672616D6503053Q004D656E757303053Q00496E64657803053Q00506167657303043Q004F726573000B4Q0036016Q00206Q000100206Q000200206Q000300206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00033Q0003043Q007469636B028Q00026Q00F03F01153Q00126A2Q0100014Q0011000100010002000640012Q000E0001000100046D3Q000E00012Q00A400026Q002E010200023Q000EA80102000E0001000200046D3Q000E00012Q00A4000200014Q00D50002000100020026320102000E0001000300046D3Q000E00012Q00A400026Q003A000200024Q00A4000200024Q00840002000100024Q00028Q000100016Q00028Q000200028Q00017Q000B3Q00030B3Q004C6F63616C506C6179657203053Q007063612Q6C03053Q007061697273030B3Q004765744368696C6472656E03043Q004E616D652Q033Q00737562026Q0014C003053Q00204C69737403053Q007461626C6503063Q00696E7365727403043Q00736F727400254Q00468Q00A400015Q00205400010001000100126A010200023Q00066B01033Q000100012Q003C3Q00014Q00640002000200030006B40002000B00013Q00046D3Q000B00010006400103000D0001000100046D3Q000D00012Q004600046Q003A000400023Q00126A010400033Q0020380005000300042Q0030000500064Q002300043Q000600046D3Q001D0001002054000900080005002038000900090006001225010B00074Q004C0009000B00020026800009001D0001000800046D3Q001D000100126A010900093Q00205400090009000A2Q003C000A5Q002054000B000800052Q007D0009000B0001000677010400120001000200046D3Q0012000100126A010400093Q0020B500040004000B4Q00058Q0004000200016Q00028Q00013Q00013Q00073Q0003093Q00506C6179657247756903043Q004D656E7503053Q004672616D6503053Q004D656E757303053Q00496E64657803053Q00506167657303043Q004F726573000B4Q0036016Q00206Q000100206Q000200206Q000300206Q000300206Q000400206Q000500206Q000600206Q00076Q00028Q00017Q00103Q00026Q005940026Q003440026Q004440026Q004E40026Q00544003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03063Q00697061697273030E3Q0046696E6446697273744368696C6403083Q00746F737472696E6703083Q004261736550617274030C3Q005472616E73706172656E637902CD5QCCEC3F2Q033Q004F7265013E3Q000640012Q00040001000100046D3Q000400010012252Q0100014Q003A000100024Q0046000100053Q0012AF000200023Q00122Q000300033Q00122Q000400043Q00122Q000500053Q00122Q000600016Q0001000500012Q002C000200023Q0012A7000300063Q00202Q00043Q00074Q000400056Q00033Q000500044Q00180001002038000800070008001225010A00094Q004C0008000A00020006B40008001800013Q00046D3Q001800012Q003C000200073Q00046D3Q001A0001000677010300110001000200046D3Q001100010006400102001D0001000100046D3Q001D00012Q003C00025Q00126A0103000A4Q003C000400014Q006400030002000500046D3Q0031000100203800080002000B001241000A000C6Q000B00076Q000A000B6Q00083Q000200062Q0008003100013Q00046D3Q00310001002038000900080008001225010B000D4Q004C0009000B00020006B40009003100013Q00046D3Q0031000100205400090008000E002632010900310001000F00046D3Q003100012Q003A000700023Q000677010300210001000200046D3Q0021000100203800030002000B001225010500104Q0012010600014Q004C0003000600020006B40003003B00013Q00046D3Q003B0001001225010400034Q003A000400023Q001225010400014Q003A000400024Q00C43Q00017Q000C3Q0003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C030E3Q0046696E6446697273744368696C6403063Q00726F636B485003093Q00546578744C6162656C03043Q005465787403083Q00746F6E756D62657203053Q006D617463682Q033Q0025642B028Q00012E3Q000640012Q00040001000100046D3Q000400012Q002C000100014Q003A000100024Q002C000100013Q0012A7000200013Q00202Q00033Q00024Q000300046Q00023Q000400044Q00110001002038000700060003001225010900044Q004C0007000900020006B40007001100013Q00046D3Q001100012Q003C000100063Q00046D3Q001300010006770102000A0001000200046D3Q000A00010006402Q0100160001000100046D3Q001600012Q003C00015Q002038000200010005001225010400064Q0012010500014Q004C0002000500020006B40002002B00013Q00046D3Q002B0001002038000300020003001225010500074Q004C0003000500020006B40003002B00013Q00046D3Q002B000100205400030002000800126A010400093Q00203800050003000A0012250107000B4Q0095010500074Q00D600043Q00020006390105002A0001000400046D3Q002A00010012250105000C4Q003A000500024Q002C000300034Q003A000300024Q00C43Q00017Q00073Q0003053Q007061697273030E3Q0047657444657363656E64616E747303043Q004E616D652Q033Q004F72652Q033Q0049734103053Q004D6F64656C030C3Q00476574412Q74726962757465011A3Q000640012Q00040001000100046D3Q000400012Q002C000100014Q003A000100023Q00126A2Q0100013Q00203800023Q00022Q0030000200034Q002300013Q000300046D3Q00150001002054000600050003002680000600150001000400046D3Q00150001002038000600050005001225010800064Q004C0006000800020006B40006001500013Q00046D3Q00150001002038000600050007001225010800044Q00FF000600084Q002D00065Q0006772Q0100090001000200046D3Q000900012Q002C000100014Q003A000100024Q00C43Q00017Q00063Q0003083Q00746F737472696E67034Q0003043Q006773756203043Q005B25635D03053Q005B802DFF5D03013Q003F01113Q00126A2Q0100013Q0006390102000400013Q00046D3Q00040001001225010200024Q00B80001000200022Q009D012Q00013Q00202Q00013Q000300122Q000300043Q00122Q000400026Q00010004000200202Q00010001000300122Q000300053Q00122Q000400066Q0001000400026Q00014Q003A3Q00024Q00C43Q00017Q00033Q0003093Q0044656275674D6F646503053Q007072696E74030F3Q005B466F726765204D696E696E675D20020E4Q00A400025Q002054000200020001000640010200060001000100046D3Q000600010006B40001000D00013Q00046D3Q000D000100126A010200023Q001291000300036Q000400016Q00058Q0004000200024Q0003000300044Q0002000200012Q00C43Q00017Q00023Q0003043Q007469636B028Q0002113Q001229010200016Q0002000100024Q00038Q000300033Q00062Q000300070001000100046D3Q00070001001225010300024Q00D50004000200030006A30104000C0001000100046D3Q000C00012Q0012010400014Q003A000400024Q00A400046Q003F00043Q00022Q001201046Q003A000400024Q00C43Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403063Q004C6976696E6703043Q004E616D6500134Q00A48Q00113Q00010002000640012Q00060001000100046D3Q000600012Q002C000100014Q003A000100024Q00A4000100013Q002038000100010001001225010300024Q004C0001000300020006B40001001000013Q00046D3Q0010000100203800020001000100205400043Q00032Q00FF000200044Q002D00026Q002C000200024Q003A000200024Q00C43Q00017Q00073Q0003043Q006D61746803053Q00666C2Q6F72025Q0020AC40026Q004E4003063Q00737472696E6703063Q00666F726D6174030E3Q00253032643A253032643A2530326401163Q00126A2Q0100013Q0020540001000100020020F700023Q00032Q00B800010002000200126A010200013Q00205400020002000200200901033Q00030020F70003000300042Q00B800020002000200126A010300013Q00205400030003000200201501043Q00044Q00030002000200122Q000400053Q00202Q00040004000600122Q000500076Q000600016Q000700026Q000800036Q000400086Q00046Q00C43Q00019Q003Q00094Q0012012Q00014Q00D78Q00468Q00D73Q00014Q00468Q00D73Q00024Q00468Q00D73Q00034Q00C43Q00017Q00073Q0003043Q007469636B029A5Q99C93F030E3Q0046696E6446697273744368696C6403053Q00526F636B73030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637403123Q0044657363656E64616E7452656D6F76696E6700283Q00126A012Q00014Q00113Q000100022Q00A400015Q0006B40001000B00013Q00046D3Q000B00012Q00A4000100014Q00D500013Q00010026322Q01000B0001000200046D3Q000B00012Q00A400016Q003A000100024Q00D73Q00014Q00AB000100023Q00202Q00010001000300122Q000300046Q0001000300024Q00018Q00015Q00062Q0001002500013Q00046D3Q002500012Q00A4000100033Q0006402Q0100250001000100046D3Q002500012Q00122Q0100014Q00652Q0100036Q00015Q00202Q00010001000500202Q0001000100064Q000300056Q0001000300024Q000100046Q00015Q00202Q00010001000700202Q0001000100064Q000300056Q0001000300024Q000100064Q00A400016Q003A000100024Q00C43Q00017Q00093Q0003043Q007469636B026Q00E03F030E3Q0046696E6446697273744368696C64030D3Q00537061776E4C6F636174696F6E03113Q005361666548656967687444656661756C7403083Q00506F736974696F6E03093Q004D61676E697475646503103Q00537061776E436865636B526164697573030F3Q0053616665486569676874537061776E011D3Q001235000100016Q0001000100024Q00028Q00020001000200262Q000200080001000200046D3Q000800012Q00A4000200014Q003A000200024Q00D700016Q00F2000200023Q00202Q00020002000300122Q000400046Q0002000400024Q000300033Q00202Q00030003000500062Q0002001A00013Q00046D3Q001A00010020540004000200062Q001A00043Q000400202Q0004000400074Q000500033Q00202Q00050005000800062Q0004001A0001000500046D3Q001A00012Q00A4000400033Q0020540003000400092Q00D7000300014Q003A000300024Q00C43Q00017Q00023Q0003063Q00506172656E74030D3Q0043752Q72656E7443616D657261000D4Q00A47Q0006B43Q000700013Q00046D3Q000700012Q00A47Q0020545Q0001000640012Q000A0001000100046D3Q000A00012Q00A43Q00013Q0020545Q00022Q00D78Q00A48Q003A3Q00024Q00C43Q00017Q000E3Q00030A3Q0043616D6572614D6F646503043Q004E6F6E6503153Q002043616D657261206E6F7420617661696C61626C6503123Q004F726967696E616C43616D65726154797065030A3Q0043616D6572615479706503103Q0043616D657261436F2Q6E656374696F6E030A3Q00446973636F2Q6E6563740003093Q0043616D434672616D6503163Q002043616D657261204D6F646520535441525445443A2003043Q00456E756D030A3Q0053637269707461626C65030D3Q0052656E6465725374652Q70656403073Q00436F2Q6E65637400384Q00A47Q0020545Q00010026803Q00050001000200046D3Q000500012Q00C43Q00014Q00A43Q00014Q00113Q00010002000640012Q000E0001000100046D3Q000E00012Q00A4000100023Q001225010200034Q0012010300014Q007D0001000300012Q00C43Q00014Q00A4000100033Q0020540001000100040006402Q0100150001000100046D3Q001500012Q00A4000100033Q00205400023Q00050010162Q01000400022Q00A4000100033Q0020540001000100060006B40001001F00013Q00046D3Q001F00012Q00A4000100033Q00200B2Q010001000600202Q0001000100074Q0001000200014Q000100033Q00302Q0001000600082Q00A4000100033Q00300D0001000900082Q00A4000100023Q0012250102000A4Q00A400035Q0020540003000300012Q007A0002000200032Q009A2Q010002000100126A2Q01000B3Q00205400010001000500205400010001000C001016012Q000500012Q00A4000100034Q00A4000200043Q00205400020002000D00203800020002000E00066B01043Q000100052Q00A48Q00A43Q00014Q00A43Q00054Q00A43Q00064Q00A43Q00034Q004C0002000400020010162Q01000600022Q00C43Q00013Q00013Q001A3Q00030A3Q004175746F4D696E696E67030B3Q0043752Q72656E74526F636B03043Q0074797065030D3Q00476574526F636B486974626F7803083Q0066756E6374696F6E030C3Q0043616D657261486569676874030E3Q0043616D65726144697374616E6365030A3Q0043616D65726153696465030A3Q0043616D6572614D6F6465030A3Q004C6F636B54617267657403083Q00506F736974696F6E03073Q00566563746F72332Q033Q006E657703013Q0058028Q0003013Q005A03093Q004D61676E6974756465029A5Q99B93F03043Q00556E6974026Q00F0BF03063Q00434672616D6503063Q006C2Q6F6B4174030A3Q004C2Q6F6B566563746F72030B3Q005269676874566563746F72030B3Q0046697865644F2Q66736574026Q00144000954Q00A47Q0020545Q0001000640012Q00050001000100046D3Q000500012Q00C43Q00014Q00A43Q00014Q00113Q00010002000640012Q000A0001000100046D3Q000A00012Q00C43Q00014Q00A4000100024Q006C2Q01000100024Q000200036Q000300016Q00020002000200062Q000200120001000100046D3Q001200012Q00C43Q00014Q002C000300034Q00A4000400043Q0020540004000400020006B40004002100013Q00046D3Q0021000100126A010400033Q00126A010500044Q00B8000400020002002680000400210001000500046D3Q0021000100126A010400044Q00A4000500043Q0020540005000500022Q00B80004000200022Q003C000300044Q00A400045Q00206F0104000400064Q00055Q00202Q0005000500074Q00065Q00202Q0006000600084Q00075Q00202Q00070007000900262Q000700720001000A00046D3Q007200010006B40003005B00013Q00046D3Q005B000100205400070002000B00201F00080003000B4Q00090008000700122Q000A000C3Q00202Q000A000A000D00202Q000B0009000E00122Q000C000F3Q00202Q000D000900104Q000A000D000200202Q000B000A0011000E2Q0012003C0001000B00046D3Q003C0001002054000B000A0013000640010B00420001000100046D3Q0042000100126A010B000C3Q002067010B000B000D00122Q000C000F3Q00122Q000D000F3Q00122Q000E00146Q000B000E000200126A010C000C3Q0020E0000C000C000D00202Q000D000B001000122Q000E000F3Q00202Q000F000B000E4Q000F000F6Q000C000F00024Q000D000B00054Q000D0007000D00122Q000E000C3Q00202Q000E000E000D001225010F000F4Q0056001000043Q00122Q0011000F6Q000E001100024Q000D000D000E4Q000E000C00064Q000D000D000E00122Q000E00153Q00202Q000E000E00164Q000F000D6Q001000084Q004C000E00100002001016012Q0015000E00046D3Q009400010020540007000200150020C600070007001700202Q00080002001500202Q00080008001800202Q00090002000B4Q000A000700054Q00090009000A00122Q000A000C3Q00202Q000A000A000D00122Q000B000F6Q000C00043Q001225010D000F4Q00AA000A000D00024Q00090009000A4Q000A000800064Q00090009000A00122Q000A00153Q00202Q000A000A00164Q000B00093Q00202Q000C0002000B4Q000A000C000200104Q0015000A00046D3Q009400012Q00A400075Q002054000700070009002680000700940001001900046D3Q0094000100205400070002001500208A00070007001700202Q00080002001500202Q00080008001800202Q00090002000B4Q000A000700054Q00090009000A00122Q000A000C3Q00202Q000A000A000D00122Q000B000F6Q000C00043Q00122Q000D000F6Q000A000D00024Q00090009000A4Q000A000800064Q00090009000A00202Q000A0002000B00122Q000B000C3Q00202Q000B000B000D00122Q000C000F3Q00122Q000D001A3Q00122Q000E000F6Q000B000E00024Q000A000A000B00122Q000B00153Q00202Q000B000B00164Q000C00096Q000D000A6Q000B000D000200104Q0015000B2Q00C43Q00017Q000A3Q0003103Q0043616D657261436F2Q6E656374696F6E030A3Q00446973636F2Q6E6563740003143Q002043616D657261204D6F64652053544F2Q50454403123Q004F726967696E616C43616D65726154797065030A3Q0043616D6572615479706503153Q002043616D65726120726573746F72656420746F3A2003083Q00746F737472696E6703043Q00456E756D03063Q00437573746F6D00294Q00A47Q0020545Q00010006B43Q000D00013Q00046D3Q000D00012Q00A47Q0020EE5Q000100206Q00026Q000200019Q0000304Q000100036Q00013Q00122Q000100048Q000200012Q00A43Q00024Q00113Q000100022Q00A400015Q0020540001000100050006B40001002200013Q00046D3Q002200010006B43Q002200013Q00046D3Q002200012Q00A400015Q0020882Q010001000500104Q000600014Q00015Q00302Q0001000500034Q000100013Q00122Q000200073Q00122Q000300083Q00202Q00043Q00064Q0003000200024Q0002000200034Q00010002000100044Q002800010006B43Q002800013Q00046D3Q0028000100126A2Q0100093Q00205400010001000600205400010001000A001016012Q000600012Q00C43Q00017Q00073Q0003023Q005F4703053Q00466F726765030B3Q0043616D6572615368616B65030A3Q00497344697361626C656403053Q007063612Q6C03123Q0043616D6572615368616B65526573746F726503063Q00456E61626C65001D3Q00126A012Q00013Q0020545Q00020006B43Q000700013Q00046D3Q0007000100126A012Q00013Q0020545Q00020020545Q0003000640012Q000A0001000100046D3Q000A00012Q00C43Q00014Q002C000100013Q00205400023Q00040006B40002001400013Q00046D3Q0014000100126A010200053Q00205400033Q00042Q00640002000200030006B40002001400013Q00046D3Q001400012Q003C000100034Q00A400025Q00101601020006000100205400023Q00070006B40002001C00013Q00046D3Q001C000100126A010200053Q00205400033Q00072Q009A0102000200012Q00C43Q00017Q000A3Q0003023Q005F4703053Q00466F726765030B3Q0043616D6572615368616B6503123Q0043616D6572615368616B65526573746F7265002Q0103073Q0044697361626C6503053Q007063612Q6C010003063Q00456E61626C6500223Q00126A012Q00013Q0020545Q00020006B43Q000700013Q00046D3Q0007000100126A012Q00013Q0020545Q00020020545Q00032Q00A400015Q0020540001000100042Q00A400025Q00300D0002000400050006B43Q000F00013Q00046D3Q000F0001002680000100100001000500046D3Q001000012Q00C43Q00013Q002680000100190001000600046D3Q0019000100205400023Q00070006B40002001900013Q00046D3Q0019000100126A010200083Q00205400033Q00072Q009A01020002000100046D3Q00210001002680000100210001000900046D3Q0021000100205400023Q000A0006B40002002100013Q00046D3Q0021000100126A010200083Q00205400033Q000A2Q009A0102000200012Q00C43Q00017Q000E3Q0003043Q007469636B03043Q0074696D65026Q00144003063Q00686974626F7803063Q00506172656E74030E3Q00497344657363656E64616E744F660003053Q007061697273030E3Q0047657444657363656E64616E747303043Q004E616D6503063Q00486974626F782Q033Q0049734103083Q004261736550617274030D3Q00537061776E4C6F636174696F6E014D3Q000640012Q00040001000100046D3Q000400012Q002C000100014Q003A000100024Q00A400016Q00A6000100013Q0006B40001001F00013Q00046D3Q001F000100126A010200014Q00110002000100020020540003000100022Q00D50002000200030026320102001F0001000300046D3Q001F00010020540002000100040006B40002001D00013Q00046D3Q001D00010020540002000100040020540002000200050006B40002001D00013Q00046D3Q001D00010020540002000100040020380002000200062Q003C00046Q004C0002000400020006B40002001D00013Q00046D3Q001D00010020540002000100042Q003A000200024Q00A400025Q00200900023Q00072Q002C000200023Q0012A7000300083Q00202Q00043Q00094Q000400056Q00033Q000500044Q002F000100205400080007000A0026800008002F0001000B00046D3Q002F000100203800080007000C001225010A000D4Q004C0008000A00020006B40008002F00013Q00046D3Q002F00012Q003C000200073Q00046D3Q00310001000677010300250001000200046D3Q00250001000640010200440001000100046D3Q0044000100126A010300083Q00203800043Q00092Q0030000400054Q002300033Q000500046D3Q0042000100203800080007000C001225010A000D4Q004C0008000A00020006B40008004200013Q00046D3Q0042000100205400080007000A0026A7010800420001000E00046D3Q004200012Q003C000200073Q00046D3Q00440001000677010300380001000200046D3Q003800012Q00A400036Q008D01043Q000200102Q00040004000200122Q000500016Q00050001000200102Q0004000200054Q00033Q00044Q000200028Q00017Q00053Q0003053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03043Q004E616D6501153Q000640012Q00040001000100046D3Q000400012Q002C000100014Q003A000100023Q00126A2Q0100013Q00203800023Q00022Q0030000200034Q002300013Q000300046D3Q00100001002038000600050003001225010800044Q004C0006000800020006B40006001000013Q00046D3Q001000010020540006000500052Q003A000600023Q0006772Q0100090001000200046D3Q000900012Q002C000100014Q003A000100024Q00C43Q00017Q00103Q0003043Q007469636B03043Q0074696D65027Q004003043Q006F72657303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C030E3Q0047657444657363656E64616E747303043Q004E616D652Q033Q004F7265030C3Q00476574412Q74726962757465034Q0003053Q007461626C6503043Q0066696E6403063Q00696E73657274014C3Q000640012Q00040001000100046D3Q000400012Q004600016Q003A000100024Q00A400016Q00A6000100013Q00126A010200014Q00110002000100020006B40001001000013Q00046D3Q001000010020540003000100022Q00D5000300020003002632010300100001000300046D3Q001000010020540003000100042Q003A000300024Q004600036Q002C000400043Q0012A7000500053Q00202Q00063Q00064Q000600076Q00053Q000700044Q001E0001002038000A00090007001225010C00084Q004C000A000C00020006B4000A001E00013Q00046D3Q001E00012Q003C000400093Q00046D3Q00200001000677010500170001000200046D3Q00170001000640010400230001000100046D3Q002300012Q003C00045Q00126A010500053Q0020380006000400092Q0030000600074Q002300053Q000700046D3Q00430001002054000A0009000A002680000A00430001000B00046D3Q00430001002038000A00090007001225010C00084Q004C000A000C00020006B4000A004300013Q00046D3Q00430001002038000A0009000C001225010C000B4Q004C000A000C00020006B4000A004300013Q00046D3Q004300010026A7010A00430001000D00046D3Q0043000100126A010B000E3Q0020FA000B000B000F4Q000C00036Q000D000A6Q000B000D000200062Q000B00430001000100046D3Q0043000100126A010B000E3Q002054000B000B00102Q003C000C00034Q003C000D000A4Q007D000B000D0001000677010500280001000200046D3Q002800012Q00A400056Q008E01063Q000200102Q00060004000300102Q0006000200024Q00053Q00064Q000300028Q00017Q000B3Q00030E3Q0046696E6446697273744368696C6403053Q00526F636B7303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C028Q0003053Q007461626C6503043Q0066696E64026Q00F03F01394Q00D100018Q00025Q00202Q00020002000100122Q000400026Q00020004000200062Q000200080001000100046D3Q000800012Q003A000100023Q00126A010300033Q0020380004000200042Q0030000400054Q002300033Q000500046D3Q00350001002038000800070005001225010A00064Q004C0008000A0002000640010800170001000100046D3Q00170001002038000800070005001225010A00074Q004C0008000A00020006B40008003500013Q00046D3Q0035000100126A010800033Q0020380009000700042Q00300009000A4Q002300083Q000A00046D3Q003300012Q00A4000D00014Q003C000E000C4Q00B8000D000200020006B4000D003300013Q00046D3Q003300010006B43Q002D00013Q00046D3Q002D00012Q002E010E5Q0026A7010E002D0001000800046D3Q002D000100126A010E00093Q0020CE000E000E000A4Q000F8Q0010000D6Q000E0010000200062Q000E003300013Q00046D3Q003300012Q00A6000E0001000D000640010E00310001000100046D3Q00310001001225010E00083Q002034000E000E000B2Q003F0001000D000E0006770108001C0001000200046D3Q001C00010006770103000D0001000200046D3Q000D00012Q003A000100024Q00C43Q00017Q000D3Q00028Q0003203Q00F09F938A202873656C65637420726F636B7320746F20732Q6520636F756E742903063Q0069706169727303053Q007461626C6503063Q00696E7365727403023Q003A20026Q00F03F030C3Q00F09F938A20466F756E643A20030C3Q00F09F938A20546F74616C3A2003023Q00202803063Q00636F6E63617403023Q002C2003013Q002901333Q0006B43Q000500013Q00046D3Q000500012Q002E2Q015Q002680000100070001000100046D3Q000700010012252Q0100024Q003A000100024Q00A400016Q001C00028Q0001000200024Q00025Q00122Q000300013Q00122Q000400036Q00058Q00040002000600044Q001D00012Q00A6000900010008000640010900140001000100046D3Q00140001001225010900014Q00E9000300030009001224010A00043Q00202Q000A000A00054Q000B00026Q000C00083Q00122Q000D00066Q000E00096Q000C000C000E4Q000A000C0001000677010400100001000200046D3Q001000012Q002E01045Q002680000400270001000700046D3Q00270001001225010400084Q003C000500034Q007A0004000400052Q003A000400023Q00046D3Q00320001001225010400094Q0015000500033Q00122Q0006000A3Q00122Q000700043Q00202Q00070007000B4Q000800023Q00122Q0009000C6Q00070009000200122Q0008000D6Q0004000400084Q000400024Q00C43Q00017Q00013Q0003053Q007063612Q6C000A4Q00A47Q0006B43Q000900013Q00046D3Q0009000100126A012Q00013Q00066B2Q013Q000100012Q00A48Q009A012Q000200012Q002C8Q00D78Q00C43Q00013Q00013Q00023Q0003043Q007461736B03063Q0063616E63656C00053Q0012923Q00013Q00206Q00024Q00019Q00000200016Q00017Q00023Q0003043Q007461736B03053Q00737061776E000B4Q00A48Q008C3Q0001000100126A012Q00013Q0020545Q000200066B2Q013Q000100032Q00A43Q00024Q00A43Q00034Q00A43Q00044Q00B83Q000200022Q00D73Q00014Q00C43Q00013Q00013Q00083Q00030A3Q004175746F4D696E696E6703043Q007461736B03043Q0077616974026Q000840030E3Q00526F636B436F756E744C6162656C030D3Q0053656C6563746564526F636B73028Q0003053Q007063612Q6C001E4Q00A47Q0020545Q00010006B43Q001D00013Q00046D3Q001D000100126A012Q00023Q0020A0014Q000300122Q000100048Q000200019Q0000206Q000100064Q000D0001000100046D3Q000D000100046D3Q001D00012Q00A43Q00013Q0020545Q00050006B45Q00013Q00046D5Q00012Q00A47Q0020545Q00062Q002E016Q000EA801073Q00013Q00046D5Q000100126A012Q00083Q00066B2Q013Q000100032Q00A43Q00014Q00A43Q00024Q00A48Q009A012Q0002000100046D5Q00012Q00C43Q00013Q00013Q00033Q00030E3Q00526F636B436F756E744C6162656C2Q033Q00536574030D3Q0053656C6563746564526F636B7300094Q0041016Q00206Q000100206Q00024Q000200016Q000300023Q00202Q0003000300034Q000200039Q0000016Q00017Q000B3Q00030B3Q005A6F6E65456E61626C6564030A3Q005A6F6E6543656E74657203013Q005803083Q005A6F6E654C65667403093Q005A6F6E65526967687403013Q005903083Q005A6F6E65446F776E03063Q005A6F6E65557003013Q005A03093Q005A6F6E6546726F6E7403083Q005A6F6E654261636B01364Q00A400015Q0020540001000100010006402Q0100060001000100046D3Q000600012Q00122Q0100014Q003A000100024Q00A400015Q0020F000010001000200202Q00023Q000300202Q0003000100034Q00045Q00202Q0004000400044Q00030003000400062Q000300320001000200046D3Q0032000100205400023Q00030020930103000100034Q00045Q00202Q0004000400054Q00030003000400062Q000200320001000300046D3Q0032000100205400023Q000600209C0103000100064Q00045Q00202Q0004000400074Q00030003000400062Q000300320001000200046D3Q0032000100205400023Q00060020930103000100064Q00045Q00202Q0004000400084Q00030003000400062Q000200320001000300046D3Q0032000100205400023Q000900209C0103000100094Q00045Q00202Q00040004000A4Q00030003000400062Q000300320001000200046D3Q0032000100205400023Q00090020760003000100094Q00045Q00202Q00040004000B4Q00030003000400062Q000200020001000300046D3Q003300012Q001301026Q0012010200014Q003A000200024Q00C43Q00017Q00083Q00030C3Q00536B692Q706564526F636B73026Q00594000030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B7303043Q007479706503063Q006E756D62657203043Q007469636B01354Q00A400015Q0020540001000100012Q00A6000100013Q0006402Q0100070001000100046D3Q000700012Q00122Q016Q003A000100024Q00A4000100014Q003C00026Q00B80001000200020006B40001001900013Q00046D3Q00190001000E69010200190001000100046D3Q001900012Q00A400025Q00204F00020002000100202Q00023Q00034Q00025Q00202Q00020002000400202Q00023Q00034Q00025Q00202Q00020002000500202Q00023Q00034Q00028Q000200024Q00A400025Q0020540002000200012Q00A6000200023Q00126A010300064Q003C000400024Q00B8000300020002002680000300320001000700046D3Q0032000100126A010300084Q00110003000100020006B3000200300001000300046D3Q003000012Q00A400035Q00204F00030003000100202Q00033Q00034Q00035Q00202Q00030003000400202Q00033Q00034Q00035Q00202Q00030003000500202Q00033Q00034Q00038Q000300024Q0012010300014Q003A000300024Q0012010300014Q003A000300024Q00C43Q00017Q000C3Q0003043Q007469636B028Q0003053Q007061697273030C3Q00536B692Q706564526F636B7303063Q00506172656E74026Q00594000030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B73026Q00F03F03043Q007479706503063Q006E756D62657200343Q0012173Q00018Q0001000200122Q000100023Q00122Q000200036Q00035Q00202Q0003000300044Q00020002000400044Q003000012Q00A4000700014Q003C000800054Q00B80007000200020006B40005001400013Q00046D3Q001400010020540008000500050006B40008001400013Q00046D3Q001400010006B40007001F00013Q00046D3Q001F0001000E690106001F0001000700046D3Q001F00012Q00A400085Q00201200080008000400202Q0008000500074Q00085Q00202Q00080008000800202Q0008000500074Q00085Q00202Q00080008000900202Q00080005000700202Q00010001000A00046D3Q0030000100126A0108000B4Q003C000900064Q00B8000800020002002680000800300001000C00046D3Q003000010006B30006003000013Q00046D3Q003000012Q00A400085Q00201200080008000400202Q0008000500074Q00085Q00202Q00080008000800202Q0008000500074Q00085Q00202Q00080008000900202Q00080005000700202Q00010001000A000677010200080001000200046D3Q000800012Q003A000100024Q00C43Q00017Q000B3Q0003043Q007469636B028Q0003053Q007061697273030F3Q004F7265536B69704E6F74696669656403063Q00506172656E7400026Q00F03F030D3Q004F7265436865636B4C6576656C03043Q007479706503063Q006E756D626572025Q00C0724000303Q0012173Q00018Q0001000200122Q000100023Q00122Q000200036Q00035Q00202Q0003000300044Q00020002000400044Q002C00010006B40005000D00013Q00046D3Q000D0001002054000700050005000640010700120001000100046D3Q001200012Q00A400075Q00205400070007000400200900070005000600203400010001000700046D3Q002C00012Q00A4000700014Q003C000800054Q00B80007000200020006B40007002000013Q00046D3Q002000012Q00A4000800023Q0020540008000800080006A3010800200001000700046D3Q002000012Q00A400085Q00205400080008000400200900080005000600203400010001000700046D3Q002C000100126A010800094Q003C000900064Q00B80008000200020026800008002C0001000A00046D3Q002C00012Q00D500083Q0006000EA8010B002C0001000800046D3Q002C00012Q00A400085Q002054000800080004002009000800050006002034000100010007000677010200080001000200046D3Q000800012Q003A000100024Q00C43Q00017Q00123Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7303063Q006970616972732Q01030D3Q0053656C6563746564526F636B7303053Q007461626C6503063Q00696E73657274030E3Q00526F636B5072696F726974696573026Q00F03F030C3Q00526F636B44726F70646F776E03053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403113Q00526F636B73207265667265736865643A2003083Q004475726174696F6E027Q0040030F3Q004C617374526F636B5265667265736803043Q007469636B01574Q00A400016Q0077000200016Q0001000200014Q000100013Q00202Q00010001000100062Q0001003900013Q00046D3Q003900012Q004600015Q00126A010200024Q00A4000300024Q006400020002000400046D3Q000D00010020090001000600030006770102000C0001000200046D3Q000C00012Q004600025Q00120D010300026Q000400013Q00202Q0004000400044Q00030002000500044Q001D00012Q00A60008000100070006B40008001D00013Q00046D3Q001D000100126A010800053Q0020540008000800062Q003C000900024Q003C000A00074Q007D0008000A0001000677010300150001000200046D3Q001500012Q002E010300024Q00A4000400013Q0020540004000400042Q002E010400043Q000659000300390001000400046D3Q003900012Q00A4000300013Q0010160103000400022Q00A4000300014Q004600045Q00101601030007000400120D010300026Q000400013Q00202Q0004000400044Q00030002000500044Q003700012Q00A4000800013Q0020980108000800074Q000900013Q00202Q0009000900044Q000900096Q00090009000600202Q0009000900084Q0008000700090006770103002F0001000200046D3Q002F00012Q00A4000100033Q0006B40001004600013Q00046D3Q004600012Q00A4000100033Q0020540001000100090006B40001004600013Q00046D3Q0046000100126A2Q01000A3Q00066B01023Q000100032Q00A43Q00034Q00A43Q00024Q00A43Q00014Q009A2Q0100020001000640012Q00520001000100046D3Q005200012Q00A4000100044Q006101023Q000300302Q0002000B000C00122Q0003000E6Q000400026Q000400046Q00030003000400102Q0002000D000300302Q0002000F00104Q0001000200012Q00A4000100053Q00126A010200124Q00110002000100020010162Q01001100022Q00C43Q00013Q00013Q00063Q00030C3Q00526F636B44726F70646F776E03073Q0052656672657368028Q0003123Q00284E6F20726F636B7320696E206172656129030D3Q0053656C6563746564526F636B732Q033Q00536574001A4Q006A7Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200046D3Q000A00012Q00A4000200013Q0006400102000D0001000100046D3Q000D00012Q0046000200013Q001225010300044Q00CD0002000100012Q007D3Q000200012Q00A43Q00023Q0020545Q00052Q002E016Q000EA80103001900013Q00046D3Q001900012Q00A47Q0020E75Q000100206Q00064Q000200023Q00202Q0002000200056Q000200012Q00C43Q00017Q00083Q0003043Q007469636B03083Q00746F6E756D62657203133Q00526F636B52656672657368496E74657276616C028Q0003183Q00526F636B526566726573684E6F54617267657444656C6179030F3Q004C617374526F636B52656672657368030D3Q004E6F54617267657453696E63650001313Q0006392Q01000400013Q00046D3Q0004000100126A2Q0100014Q001100010001000200126A010200024Q00A400035Q0020540003000300032Q00B80002000200020006400102000B0001000100046D3Q000B0001001225010200043Q00126A010300024Q00A400045Q0020540004000400052Q00B8000300020002000640010300120001000100046D3Q00120001001225010300043Q000EA8010400200001000200046D3Q002000012Q00A4000400013Q002054000400040006000640010400190001000100046D3Q00190001001225010400044Q00D50004000100040006B3000200200001000400046D3Q002000012Q00A4000400024Q0012010500014Q009A0104000200012Q00C43Q00014Q00A4000400013Q0020540004000400070006B40004003000013Q00046D3Q00300001000EA8010400300001000300046D3Q003000012Q00A4000400013Q0020540004000400072Q00D50004000100040006B3000300300001000400046D3Q003000012Q00A4000400024Q0012010500014Q009A0104000200012Q00A4000400013Q00300D0004000700082Q00C43Q00017Q00033Q0003153Q005072696F7269747954797065432Q6F6C646F776E7303043Q007469636B00011B3Q0006B43Q000600013Q00046D3Q000600012Q00A400015Q0020540001000100010006402Q0100080001000100046D3Q000800012Q00122Q016Q003A000100024Q00A400015Q0020540001000100012Q00A6000100013Q0006402Q01000F0001000100046D3Q000F00012Q001201026Q003A000200023Q00126A010200024Q00110002000100020006B3000100180001000200046D3Q001800012Q00A400025Q00205400020002000100200900023Q00032Q001201026Q003A000200024Q0012010200014Q003A000200024Q00C43Q00017Q00033Q00028Q0003153Q005072696F7269747954797065432Q6F6C646F776E7303043Q007469636B02153Q0006B43Q000600013Q00046D3Q000600010006B40001000600013Q00046D3Q000600010026D8000100070001000100046D3Q000700012Q00C43Q00014Q00A400025Q0020540002000200020006400102000E0001000100046D3Q000E00012Q00A400026Q004600035Q0010160102000200032Q00A400025Q0020F500020002000200122Q000300036Q0003000100024Q0003000300014Q00023Q00032Q00C43Q00017Q00023Q00030C3Q004D617463686564526F636B730001063Q0006B43Q000500013Q00046D3Q000500012Q00A400015Q00205400010001000100200900013Q00022Q00C43Q00017Q00023Q00030F3Q004F7265536B69704E6F7469666965640001093Q0006B43Q000800013Q00046D3Q000800012Q00A400015Q00205400010001000100200900013Q00022Q00A4000100014Q003C00026Q009A2Q01000200012Q00C43Q00017Q00023Q00030F3Q004F7265536B69704E6F7469666965640001063Q0006B43Q000500013Q00046D3Q000500012Q00A400015Q00205400010001000100200900013Q00022Q00C43Q00017Q00093Q00030E3Q00526F636B4F726546696C7465727303063Q0069706169727303043Q00526F636B03043Q004F726573028Q0003043Q00736C6F7403113Q00557365476C6F62616C46612Q6C6261636B030C3Q0053656C65637465644F72657303063Q00676C6F62616C01343Q000640012Q00040001000100046D3Q000400012Q002C000100024Q000F2Q0100034Q00A400015Q0020540001000100010006B40001002000013Q00046D3Q0020000100126A2Q0100024Q00A400025Q0020540002000200012Q006400010002000300046D3Q001E00010006B40005001E00013Q00046D3Q001E00010020540006000500030006680006001E00013Q00046D3Q001E00010020540006000500040006B40006001E00013Q00046D3Q001E00010020540006000500042Q002E010600063Q000EA80105001E0001000600046D3Q001E0001002054000600050004001225010700064Q003C000800044Q007A0007000700082Q000F010600033Q0006772Q01000D0001000200046D3Q000D00012Q00A400015Q0020540001000100070006B40001003100013Q00046D3Q003100012Q00A400015Q0020540001000100080006B40001003100013Q00046D3Q003100012Q00A400015Q0020540001000100082Q002E2Q0100013Q000EA8010500310001000100046D3Q003100012Q00A400015Q002054000100010008001225010200094Q000F2Q0100034Q002C000100024Q000F2Q0100034Q00C43Q00017Q00133Q0003113Q0041637469766546696C7465724C6162656C030B3Q0043752Q72656E74526F636B03053Q007063612Q6C028Q00030F3Q004163746976652046696C7465723A2003063Q00676C6F62616C03083Q00476C6F62616C202803083Q00746F737472696E6703063Q00206F7265732903083Q00746F6E756D62657203053Q006D61746368030B3Q005E736C6F742825642B292403053Q00536C6F742003023Q002028030E3Q00526F636B4F726546696C7465727303063Q0069706169727303043Q00526F636B03113Q00557365476C6F62616C46612Q6C6261636B030C3Q0053656C65637465644F72657301824Q00A400015Q0020540001000100010006402Q0100050001000100046D3Q000500012Q00C43Q00013Q0006392Q01001200013Q00046D3Q001200012Q00A4000100013Q0020540001000100020006B40001001100013Q00046D3Q001100012Q00A4000100024Q00A4000200013Q0020540002000200022Q00B80001000200020006402Q0100120001000100046D3Q001200012Q002C000100013Q0006402Q0100190001000100046D3Q0019000100126A010200033Q00066B01033Q000100012Q00A48Q009A0102000200012Q00C43Q00014Q00A4000200034Q003C000300014Q00640002000200030006B40002005000013Q00046D3Q005000012Q002E010400023Q000EA8010400500001000400046D3Q005000010006B40003005000013Q00046D3Q00500001001225010400053Q0026800003002E0001000600046D3Q002E00012Q003C000500043Q001243000600073Q00122Q000700086Q000800026Q00070002000200122Q000800096Q00040005000800044Q0049000100126A0105000A3Q001266010600086Q000700036Q00060002000200202Q00060006000B00122Q0008000C6Q000600086Q00053Q000200062Q0005004400013Q00046D3Q004400012Q003C000600043Q00122D0107000D3Q00122Q000800086Q000900056Q00080002000200122Q0009000E3Q00122Q000A00086Q000B00026Q000A0002000200122Q000B00096Q00040006000B00046D3Q004900012Q003C000600043Q00126A010700084Q003C000800034Q00B80007000200022Q007A00040006000700126A010500033Q00066B01060001000100022Q00A48Q003C3Q00044Q009A0105000200012Q00C43Q00014Q001D00046Q002C000400044Q00A4000500043Q00205400050005000F0006B40005006300013Q00046D3Q0063000100126A010500104Q00A4000600043Q00205400060006000F2Q006400050002000700046D3Q006100010006B40009006100013Q00046D3Q00610001002054000A00090011000668000A00610001000100046D3Q006100012Q003C000400083Q00046D3Q006300010006770105005A0001000200046D3Q005A00010006B40004006B00013Q00046D3Q006B000100126A010500033Q00066B01060002000100022Q00A48Q003C3Q00044Q009A01050002000100046D3Q008100012Q00A4000500043Q0020540005000500120006400105007D0001000100046D3Q007D00012Q00A4000500043Q0020540005000500130006B40005007D00013Q00046D3Q007D00012Q00A4000500043Q0020540005000500132Q002E010500053Q000EA80104007D0001000500046D3Q007D000100126A010500033Q00066B01060003000100012Q00A48Q009A01050002000100046D3Q0081000100126A010500033Q00066B01060004000100012Q00A48Q009A0105000200012Q00C43Q00013Q00053Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403133Q004163746976652046696C7465723A204E6F6E6500064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00023Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657400064Q0094016Q00206Q000100206Q00024Q000200018Q000200016Q00017Q00053Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403143Q004163746976652046696C7465723A20536C6F742003083Q00746F737472696E67030A3Q0020286E6F206F72657329000B4Q00D37Q00206Q000100206Q000200122Q000200033Q00122Q000300046Q000400016Q00030002000200122Q000400056Q0002000200046Q000200016Q00017Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403203Q004163746976652046696C7465723A204E6F6E652028676C6F62616C206F2Q662900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403133Q004163746976652046696C7465723A204E6F6E6500064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00053Q00030C3Q0043752Q72656E745068617365026Q001040030B3Q0043752Q72656E74526F636B03113Q004C6173744F7265536B69704E6F7469667903043Q007469636B021B3Q000639010200040001000100046D3Q000400012Q00A400025Q0020540002000200010026A7010200080001000200046D3Q000800012Q001201036Q003A000300023Q0006B43Q001400013Q00046D3Q001400012Q00A400035Q0020540003000300030006B40003001400013Q00046D3Q001400012Q00A400035Q0020540003000300030006593Q00140001000300046D3Q001400012Q001201036Q003A000300024Q00A400035Q00120A000400056Q00040001000200102Q0003000400044Q000300016Q000300028Q00017Q001B3Q00030D3Q004F7265536B69704E6F74696679030F3Q004F7265536B69704E6F74696669656403043Q007469636B03083Q00746F737472696E6703013Q002503013Q003F03043Q006D61746803053Q00666C2Q6F72028Q0003143Q004F726520536B69702028526F636B20547970652903063Q00737472696E6703063Q00666F726D617403143Q00E29D8C2025730AF09F8EAF2057616E743A20257303073Q00556E6B6E6F776E03063Q00286E6F6E652903133Q004F726520536B697020284D69736D617463682903143Q004F726520536B697020285072652D436865636B2903273Q00F09FAAA820257320402025730AF09F928E204861733A2025730AF09F8EAF2057616E743A20257303043Q006E6F6E6503103Q000AE28FB1EFB88F20536B69702025647303183Q000AE28FB1EFB88F20536B697020756E74696C20726567656E031C3Q0025732040202573207C204861733A202573207C2057616E743A20257303053Q005469746C6503083Q004F726520536B697003073Q00436F6E74656E7403083Q004475726174696F6E026Q001040087A4Q00A400085Q002054000800080001000640010800050001000100046D3Q000500012Q00C43Q00014Q00A4000800014Q003C000900064Q003C000A00074Q004C0008000A00020006400108000C0001000100046D3Q000C00012Q00C43Q00013Q0006B40006001800013Q00046D3Q001800012Q00A4000800023Q0020540008000800022Q00A6000800080006000640010800180001000100046D3Q001800012Q00A4000800023Q00205400080008000200126A010900034Q00110009000100022Q003F0008000600090006B40002002100013Q00046D3Q0021000100126A010800044Q00AC000900026Q00080002000200122Q000900056Q00080008000900062Q000800220001000100046D3Q00220001001225010800063Q0006B40005002A00013Q00046D3Q002A000100126A010900073Q0020540009000900082Q003C000A00054Q00B80009000200020006400109002B0001000100046D3Q002B0001001225010900094Q002C000A000A3Q0026803Q003C0001000A00046D3Q003C000100126A010B000B3Q002054000B000B000C001225010C000D3Q00126A010D00043Q000639010E00350001000100046D3Q00350001001225010E000E4Q00B8000D00020002000639010E00390001000400046D3Q00390001001225010E000F4Q004C000B000E00022Q003C000A000B3Q00046D3Q007000010026A7012Q00400001001000046D3Q004000010026803Q005F0001001100046D3Q005F000100126A010B000B3Q002054000B000B000C001225010C00123Q00126A010D00043Q000639010E00470001000100046D3Q00470001001225010E000E4Q00B8000D000200022Q003C000E00083Q000639010F004C0001000300046D3Q004C0001001225010F00133Q0006390110004F0001000400046D3Q004F00010012250110000F4Q004C000B001000022Q003C000A000B3Q000EA80109005B0001000900046D3Q005B00012Q003C000B000A3Q001221010C000B3Q00202Q000C000C000C00122Q000D00146Q000E00096Q000C000E00024Q000A000B000C00044Q007000012Q003C000B000A3Q001225010C00154Q007A000A000B000C00046D3Q0070000100126A010B000B3Q002054000B000B000C001225010C00163Q00126A010D00043Q000639010E00660001000100046D3Q00660001001225010E000E4Q00B8000D000200022Q003C000E00083Q000639010F006B0001000300046D3Q006B0001001225010F00133Q0006390110006E0001000400046D3Q006E00010012250110000F4Q004C000B001000022Q003C000A000B4Q00A4000B00034Q0046000C3Q0003000639010D007500013Q00046D3Q00750001001225010D00183Q001016010C0017000D001016010C0019000A00300D000C001A001B2Q009A010B000200012Q00C43Q00017Q00063Q0003063Q00697061697273034Q0003063Q00286E6F6E652903053Q007461626C6503063Q00696E736572743Q011C4Q004600015Q000640012Q00040001000100046D3Q000400012Q003A000100024Q004600025Q00126A010300014Q003C00046Q006400030002000500046D3Q001800010006B40007001800013Q00046D3Q001800010026A7010700180001000200046D3Q001800010026A7010700180001000300046D3Q001800012Q00A6000800020007000640010800180001000100046D3Q0018000100126A010800043Q0020960008000800054Q000900016Q000A00076Q0008000A000100202Q000200070006000677010300090001000200046D3Q000900012Q003A000100024Q00C43Q00017Q00083Q00026Q00F03F026Q000840030E3Q00526F636B4F726546696C7465727303043Q00526F636B0003043Q004F726573034Q0003143Q00284E6F20726F636B7320617661696C61626C6529032C3Q0026CA3Q00040001000100046D3Q00040001000EA80102000500013Q00046D3Q000500012Q00C43Q00014Q00A400035Q002054000300030003000640010300190001000100046D3Q001900012Q00A400036Q0019000400036Q00053Q000200302Q0005000400054Q00065Q00102Q0005000600064Q00063Q000200302Q0006000400054Q00075Q00102Q0006000600074Q00073Q000200302Q0007000400054Q00085Q00102Q0007000600084Q0004000300010010160103000300042Q00A400035Q0020540003000300032Q004600043Q00020006B40001002400013Q00046D3Q002400010026A72Q0100240001000700046D3Q002400010026A72Q0100240001000800046D3Q00240001000639010500250001000100046D3Q002500012Q002C000500053Q0010160104000400052Q004A000500016Q000600026Q00050002000200102Q0004000600054Q00033Q00046Q00017Q00053Q00026Q00F03F026Q000840030E3Q00526F636B4F726546696C7465727303043Q00526F636B03043Q004F726573011D3Q0026CA3Q00040001000100046D3Q00040001000EA80102000700013Q00046D3Q000700012Q002C000100014Q004600026Q000F2Q0100034Q00A400015Q0020540001000100030006B40001001000013Q00046D3Q001000012Q00A400015Q0020540001000100032Q00A6000100013Q0006402Q0100130001000100046D3Q001300012Q002C000100014Q004600026Q000F2Q0100034Q00A400015Q002Q202Q01000100034Q000100013Q00202Q00020001000400202Q00030001000500062Q0003001B0001000100046D3Q001B00012Q004600036Q000F010200034Q00C43Q00017Q00063Q0003063Q00506172656E74030D3Q0053656C6563746564526F636B73028Q0003053Q00706169727303043Q0066696E6403083Q00506F736974696F6E02373Q0006B43Q000500013Q00046D3Q0005000100205400023Q0001000640010200070001000100046D3Q000700012Q001201026Q003A000200024Q00A400026Q003C00036Q00B80002000200020006400102000E0001000100046D3Q000E00012Q001201036Q003A000300024Q00A4000300013Q0020540003000300022Q002E010300033Q000EA80103002D0001000300046D3Q002D00012Q00A4000300024Q003C00046Q00B80003000200020006B40003002D00013Q00046D3Q002D00012Q001201045Q00120D010500046Q000600013Q00202Q0006000600024Q00050002000700044Q00270001000659000300250001000900046D3Q00250001002038000A000300052Q003C000C00094Q004C000A000C00020006B4000A002700013Q00046D3Q002700012Q0012010400013Q00046D3Q002900010006770105001E0001000200046D3Q001E00010006400104002D0001000100046D3Q002D00012Q001201056Q003A000500024Q00A4000300033Q0020540004000200062Q00B8000300020002000640010300340001000100046D3Q003400012Q001201036Q003A000300024Q0012010300014Q003A000300024Q00C43Q00017Q00103Q00030F3Q005072696F72697479456E61626C6564030D3Q0053656C6563746564526F636B73027Q0040030E3Q00526F636B5072696F726974696573028Q0003053Q00706169727303083Q00506F736974696F6E030D3Q0053656C65637465644172656173030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C030E3Q0046696E6446697273744368696C6403063Q00737472696E6703063Q00666F726D6174033C3Q00205072696F726974792025642025733A20466F756E643A256420536B69703A2564204E6F4869743A256420496E76616C69643A2564204661723A2564019F4Q00A400015Q0020540001000100010006402Q0100060001000100046D3Q000600012Q002C000100014Q003A000100024Q00A400015Q0020540001000100022Q002E2Q0100013Q0026322Q01000D0001000300046D3Q000D00012Q002C000100014Q003A000100024Q00A4000100014Q003C00026Q00B80001000200020006402Q0100140001000100046D3Q001400012Q002C000200024Q003A000200024Q00A400025Q0020540002000200042Q00A60002000200010006400102001A0001000100046D3Q001A0001001225010200053Q001225010300053Q00120D010400066Q00055Q00202Q0005000500044Q00040002000600044Q002300010006A3010300230001000800046D3Q002300012Q003C000300083Q000677010400200001000200046D3Q002000010006B3000300290001000200046D3Q002900012Q002C000400044Q003A000400024Q00A4000400024Q006C0104000100024Q000500036Q000600046Q00050002000200062Q000500320001000100046D3Q003200012Q002C000600064Q003A000600023Q0020540006000500072Q00A4000700044Q0011000700010002000640010700390001000100046D3Q003900012Q002C000800084Q003A000800023Q00126A010800064Q00A400095Q0020540009000900042Q006400080002000A00046D3Q009A00010006A3010200990001000C00046D3Q009900012Q00A4000D00054Q003C000E000B4Q00B8000D00020002000640010D00990001000100046D3Q00990001001225010D00053Q001225010E00053Q001225010F00053Q001225011000053Q001225011100053Q00066B01123Q0001000F2Q00A43Q00014Q003C3Q000B4Q003C3Q000D4Q00A43Q00064Q003C3Q000E4Q00A43Q00074Q00A43Q00084Q003C3Q000F4Q00A43Q00094Q003C3Q00104Q003C3Q00064Q00A48Q003C3Q00114Q00A43Q000A4Q003C3Q000C4Q00A400135Q0020540013001300082Q002E011300133Q002680001300770001000500046D3Q0077000100126A011300063Q0020380014000700092Q0030001400154Q002300133Q001500046D3Q0074000100203800180017000A001225011A000B4Q004C0018001A00020006400118006E0001000100046D3Q006E000100203800180017000A001225011A000C4Q004C0018001A00020006B40018007400013Q00046D3Q007400012Q003C001800124Q003C001900174Q00B80018000200020006B40018007400013Q00046D3Q007400012Q003A001800023Q000677011300640001000200046D3Q0064000100046D3Q0089000100126A011300064Q00A400145Q0020540014001400082Q006400130002001500046D3Q0087000100203800180007000D2Q003C001A00174Q004C0018001A00020006B40018008700013Q00046D3Q008700012Q003C001900124Q003C001A00184Q00B80019000200020006B40019008700013Q00046D3Q008700012Q003A001900023Q0006770113007C0001000200046D3Q007C0001000EA8010500980001000D00046D3Q009800012Q00A40013000A3Q00126A0114000E3Q00205400140014000F001225011500104Q003C0016000C4Q003C0017000B4Q003C0018000D4Q003C0019000E4Q003C001A000F4Q003C001B00104Q003C001C00114Q00950114001C4Q005301133Q00012Q001D000D6Q001D000B5Q0006770108003E0001000200046D3Q003E00012Q002C000800084Q003A000800024Q00C43Q00013Q00013Q000A3Q0003053Q007061697273030B3Q004765744368696C6472656E026Q00F03F030C3Q00536B692Q706564526F636B7303083Q00506F736974696F6E03093Q004D61676E6974756465030B3Q004D696E696E6752616E676503063Q00737472696E6703063Q00666F726D6174032B3Q0020466F756E6420686967686572205020726F636B3A202573285025642920617420252E316620737475647301493Q0012A7000100013Q00202Q00023Q00024Q000200036Q00013Q000300044Q004400012Q00A400066Q003C000700054Q00B80006000200022Q00A4000700013Q000668000600440001000700046D3Q004400012Q00A4000700023Q0020A50107000700034Q000700026Q000700036Q000800056Q00070002000200062Q0007001600013Q00046D3Q001600012Q00A4000700043Q0020340007000700032Q00D7000700044Q00A4000700053Q0020540007000700042Q00A6000700070005000640010700440001000100046D3Q004400012Q00A4000700064Q003C000800054Q00B8000700020002000640010700240001000100046D3Q002400012Q00A4000800073Q0020340008000800032Q00D7000800073Q00046D3Q004400012Q00A4000800084Q003C000900054Q0012010A00014Q004C0008000A00020006400108002E0001000100046D3Q002E00012Q00A4000800093Q0020340008000800032Q00D7000800093Q00046D3Q004400012Q00A40008000A3Q00204C0109000700054Q00080008000900202Q0008000800064Q0009000B3Q00202Q00090009000700062Q0009003A0001000800046D3Q003A00012Q00A40009000C3Q0020340009000900032Q00D70009000C3Q00046D3Q004400012Q00A40009000D3Q0012DA000A00083Q00202Q000A000A000900122Q000B000A6Q000C00016Q000D000E6Q000E00086Q000A000E6Q00093Q00014Q000500023Q0006772Q0100050001000200046D3Q000500012Q002C000100014Q003A000100024Q00C43Q00017Q002C3Q0003083Q00506F736974696F6E03053Q00746F74616C028Q0003083Q006E6F486974626F7803083Q006E6F7456616C696403063Q00742Q6F46617203053Q00666F756E6403073Q00736B692Q706564030D3Q0053656C6563746564417265617303053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C030E3Q0046696E6446697273744368696C64030E3Q00526F636B5072696F72697469657303113Q005072696F726974794C6F636B556E74696C03043Q007469636B03143Q004C6173745072696F72697479526F636B5479706503043Q006D61746803043Q006875676503063Q0069706169727303043Q006469737403053Q00737061776E03063Q00506172656E7403043Q004E616D6503073Q00556E6B6E6F776E03063Q00737472696E6703063Q00666F726D617403253Q00205072696F72697479204C4F434B3A20257320696E2025732028252E316620737475647329030F3Q005072696F72697479456E61626C6564030D3Q0053656C6563746564526F636B7303053Q007461626C6503063Q00696E7365727403083Q007072696F7269747903083Q00726F636B5479706503043Q00736F7274032C3Q00205072696F7269747920526F636B3A2025732028503A25642920696E2025732028252E316620737475647329032A3Q00205072696F726974792025643A202573206E6F7420666F756E642C20747279696E67206E6578743Q2E033C3Q00204E6F207072696F7269747920726F636B7320617661696C61626C652C2066612Q6C696E67206261636B20746F20616E792076616C696420726F636B03223Q0020526F636B20466F756E643A20257320696E2025732028252E31662073747564732903363Q00205343414E205354415453207C20546F74616C3A25642056616C69643A256420536B692Q7065643A25642046696C74657265643A2564034D3Q00204445425547207C20546F74616C3A2564204E6F486974626F783A2564204E6F7456616C69643A256420542Q6F4661723A256420536B692Q7065643A2564207C20506C61796572593A252E316603013Q00590048013Q00ED9Q003Q000100024Q000100016Q00028Q00010002000200062Q000100090001000100046D3Q000900012Q002C000200024Q003A000200024Q00A4000200024Q00110002000100020006400102000F0001000100046D3Q000F00012Q002C000300034Q003A000300023Q0020540003000100012Q008D00043Q000600302Q00040002000300302Q00040004000300302Q00040005000300302Q00040006000300302Q00040007000300302Q0004000800034Q00055Q00066B01063Q000100092Q003C3Q00044Q00A43Q00034Q00A43Q00044Q00A43Q00054Q00A43Q00064Q003C3Q00034Q00A43Q00074Q00A43Q00084Q003C3Q00054Q00A4000700073Q0020540007000700092Q002E010700073Q0026800007003C0001000300046D3Q003C000100126A0107000A3Q00203800080002000B2Q0030000800094Q002300073Q000900046D3Q00390001002038000C000B000C001225010E000D4Q004C000C000E0002000640010C00360001000100046D3Q00360001002038000C000B000C001225010E000E4Q004C000C000E00020006B4000C003900013Q00046D3Q003900012Q003C000C00064Q003C000D000B4Q009A010C000200010006770107002C0001000200046D3Q002C000100046D3Q004B000100126A0107000A4Q00A4000800073Q0020540008000800092Q006400070002000900046D3Q00490001002038000C0002000F2Q003C000E000B4Q004C000C000E00020006B4000C004900013Q00046D3Q004900012Q003C000D00064Q003C000E000C4Q009A010D00020001000677010700410001000200046D3Q004100012Q001201075Q00120D0108000A6Q000900073Q00202Q0009000900104Q00080002000A00044Q005300012Q0012010700013Q00046D3Q00550001000677010800510001000100046D3Q005100012Q00A4000800043Q0020540008000800110006B40008008D00013Q00046D3Q008D00012Q00A4000800043Q00205400080008001100126A010900124Q00110009000100020006A30109008D0001000800046D3Q008D00012Q00A4000800043Q0020540008000800130006B40008008D00013Q00046D3Q008D00012Q00A4000800043Q0020540008000800132Q00A60009000500080006B40009008D00013Q00046D3Q008D00012Q002E010A00093Q000EA80103008D0001000A00046D3Q008D00012Q002C000A000A3Q001251000B00143Q00202Q000B000B001500122Q000C00166Q000D00096Q000C0002000E00044Q007700010020540011001000170006A3011100770001000B00046D3Q00770001002054000B00100017002054000A00100018000677010C00720001000200046D3Q007200010006B4000A008D00013Q00046D3Q008D0001002054000C000A00190006B4000C008200013Q00046D3Q00820001002054000C000A0019002054000C000C001A000640010C00830001000100046D3Q00830001001225010C001B4Q00A4000D00093Q00120F000E001C3Q00202Q000E000E001D00122Q000F001E6Q001000086Q0011000C6Q0012000B6Q000E00126Q000D3Q00014Q000A00024Q00A4000800073Q00205400080008001F0006B4000800F400013Q00046D3Q00F400010006B4000700F400013Q00046D3Q00F400012Q00A4000800073Q0020540008000800202Q002E010800083Q000EA8010300F40001000800046D3Q00F400012Q004600085Q00120D010900166Q000A00073Q00202Q000A000A00204Q00090002000B00044Q00AB00012Q00A4000E00073Q002054000E000E00102Q00A6000E000E000D000640010E00A40001000100046D3Q00A40001001225010E00033Q00126A010F00213Q002040000F000F00224Q001000086Q00113Q000200102Q00110023000E00102Q00110024000D4Q000F001100010006770109009E0001000200046D3Q009E000100126A010900213Q0020540009000900252Q003C000A00083Q0002BC000B00014Q005B0009000B000100122Q000900166Q000A00086Q00090002000B00044Q00EF0001002054000E000D00242Q0096010F0005000E4Q0010000A6Q0011000E6Q00100002000200062Q001000BE00013Q00046D3Q00BE00012Q002C000F000F3Q0006B4000F00E700013Q00046D3Q00E700012Q002E0110000F3Q000EA8010300E70001001000046D3Q00E700012Q002C001000103Q001251001100143Q00202Q00110011001500122Q001200166Q0013000F6Q00120002001400044Q00CF00010020540017001600170006A3011700CF0001001100046D3Q00CF0001002054001100160017002054001000160018000677011200CA0001000200046D3Q00CA00010006B4001000EF00013Q00046D3Q00EF00010020540012001000190006B4001200DA00013Q00046D3Q00DA000100205400120010001900205400120012001A000640011200DB0001000100046D3Q00DB00010012250112001B4Q00A4001300093Q0012670014001C3Q00202Q00140014001D00122Q001500266Q0016000E3Q00202Q0017000D00234Q001800126Q001900116Q001400196Q00133Q00014Q001000023Q00046D3Q00EF00012Q00A4001000093Q00126A0111001C3Q00205400110011001D001225011200273Q0020540013000D00232Q003C0014000E4Q0095011100144Q005301103Q0001000677010900B60001000200046D3Q00B600012Q00A4000900093Q001225010A00284Q009A0109000200012Q002C000800083Q001251000900143Q00202Q00090009001500122Q000A000A6Q000B00056Q000A0002000C00044Q000C2Q012Q00A4000F000A4Q003C0010000D4Q00B8000F000200020006B4000F003Q013Q00046D3Q003Q012Q002C000E000E3Q00126A010F00164Q003C0010000E4Q0064000F0002001100046D3Q000A2Q010020540014001300170006A30114000A2Q01000900046D3Q000A2Q01002054000900130017002054000800130018000677010F00052Q01000200046D3Q00052Q01000677010A00FB0001000200046D3Q00FB00010006B4000800372Q013Q00046D3Q00372Q01002054000A000800190006B4000A00172Q013Q00046D3Q00172Q01002054000A00080019002054000A000A001A000640010A00182Q01000100046D3Q00182Q01001225010A001B4Q00A4000B00093Q0012B2000C001C3Q00202Q000C000C001D00122Q000D00296Q000E00086Q000F00086Q000E0002000200062Q000E00222Q01000100046D3Q00222Q01001225010E001B4Q003C000F000A4Q00E6001000096Q000C00106Q000B3Q000100202Q000B00040008000E2Q0003002C2Q01000B00046D3Q002C2Q01002054000B00040005000EA8010300462Q01000B00046D3Q00462Q012Q00A4000B00093Q00123D000C001C3Q00202Q000C000C001D00122Q000D002A3Q00202Q000E0004000200202Q000F0004000700202Q00100004000800202Q0011000400054Q000C00116Q000B3Q000100044Q00462Q01002054000A00040002000EA8010300462Q01000A00046D3Q00462Q012Q00A4000A00093Q00120C010B001C3Q00202Q000B000B001D00122Q000C002B3Q00202Q000D0004000200202Q000E0004000400202Q000F0004000500202Q00100004000600202Q00110004000800202Q00120003002C4Q000B00126Q000A3Q00012Q003A000800024Q00C43Q00013Q00023Q00113Q0003053Q007061697273030B3Q004765744368696C6472656E03053Q00746F74616C026Q00F03F03073Q00736B692Q706564030C3Q00536B692Q706564526F636B7303083Q006E6F486974626F7803083Q006E6F7456616C696403083Q00506F736974696F6E03093Q004D61676E6974756465030B3Q004D696E696E6752616E676503063Q00742Q6F46617203053Q007461626C6503063Q00696E7365727403053Q00737061776E03043Q006469737403053Q00666F756E64015A3Q0012A7000100013Q00202Q00023Q00024Q000200036Q00013Q000300044Q005700012Q00A400066Q00E200075Q00202Q00070007000300202Q00070007000400102Q0006000300074Q000600016Q000700056Q00060002000200062Q0006001400013Q00046D3Q001400012Q00A400066Q00A400075Q0020540007000700050020340007000700040010160106000500072Q00A4000600023Q0020540006000600062Q00A6000600060005000640010600570001000100046D3Q005700012Q00A4000600034Q003C000700054Q00B8000600020002000640010600240001000100046D3Q002400012Q00A400076Q005201085Q00202Q00080008000700202Q00080008000400102Q00070007000800044Q005700012Q00A4000700044Q003C000800054Q0012010900014Q004C000700090002000640010700300001000100046D3Q003000012Q00A400076Q005201085Q00202Q00080008000800202Q00080008000400102Q00070008000800044Q005700012Q00A4000700053Q00204C0108000600094Q00070007000800202Q00070007000A4Q000800063Q00202Q00080008000B00062Q0008003E0001000700046D3Q003E00012Q00A400086Q005201095Q00202Q00090009000C00202Q00090009000400102Q0008000C000900044Q005700012Q00A4000800074Q003C000900054Q00B80008000200020006B40008005700013Q00046D3Q005700012Q00A4000900084Q00A60009000900080006400109004A0001000100046D3Q004A00012Q00A4000900084Q0046000A6Q003F00090008000A00126A0109000D3Q0020E100090009000E4Q000A00086Q000A000A00084Q000B3Q000200102Q000B000F000500102Q000B001000074Q0009000B00014Q00098Q000A5Q00202Q000A000A001100202Q000A000A000400102Q00090011000A0006772Q0100050001000200046D3Q000500012Q00C43Q00017Q00013Q0003083Q007072696F7269747902083Q00205400023Q00010020540003000100010006D4000300050001000200046D3Q000500012Q001301026Q0012010200014Q003A000200024Q00C43Q00017Q00233Q00030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D6503043Q007469636B030B3Q0043752Q72656E74526F636B026Q00F03F030C3Q0043752Q72656E745068617365028Q00030D3Q004C6F636B65644D696E65506F730003063Q00737472696E6703063Q00666F726D617403213Q0020535455434B204C313A20506861736520726573657420286D696E65733A25642903123Q004D696E657353696E636548504368616E6765027Q004003083Q00506F736974696F6E03093Q004D61676E6974756465029A5Q99B93F03043Q00556E6974030E3Q00537475636B446574656374696F6E030E3Q00476C6974636844697374616E636503063Q00434672616D652Q033Q006E6577032D3Q0020535455434B204C323A20476C69746368202B256420737475647320286D696E65733A25642C204C3223256429030E3Q004C32412Q74656D7074436F756E74033E3Q0020535455434B204C323A204F2Q6673657420742Q6F20736D612Q6C2C20736B692Q70696E6720676C69746368206D6F766520746F2061766F6964204E614E026Q00084003333Q0020535455434B204C324C333A20457363616C6174696E672061667465722033206661696C6564204C3220612Q74656D70747321030A3Q00466C696768744D6F646503053Q0042656C6F7703063Q0048656967687403073Q00566563746F7233026Q00104003243Q0020535455434B204C333A20466F7263652074656C65706F727420286D696E65733A25642903043Q006D61746803053Q00666C2Q6F72018E4Q00A400015Q0010162Q0100014Q00A400015Q00126A010200034Q00110002000100020010162Q01000200022Q00A4000100014Q00110001000100022Q00A4000200024Q003C000300014Q00B80002000200022Q00A400035Q0020540003000300040006FE000400120001000300046D3Q001200012Q00A4000400034Q003C000500034Q00B8000400020002000640010200150001000100046D3Q001500012Q00C43Q00013Q0026803Q00240001000500046D3Q002400012Q00A400055Q00300D0005000600072Q00A400055Q00300D0005000800092Q00A4000500043Q00126A0106000A3Q00205400060006000B0012250107000C4Q00A400085Q00205400080008000D2Q0095010600084Q005301053Q000100046D3Q008500010026803Q005D0001000E00046D3Q005D00010006B40004005D00013Q00046D3Q005D000100205400050004000F00205400060002000F2Q00D5000500050006002054000600050010000EA8011100480001000600046D3Q0048000100205400070005001200205800080002000F4Q000900053Q00202Q00090009001300202Q0009000900144Q0009000700094Q00080008000900122Q000900153Q00202Q0009000900164Q000A00086Q0009000200020010160102001500092Q00C5000900043Q00122Q000A000A3Q00202Q000A000A000B00122Q000B00176Q000C00053Q00202Q000C000C001300202Q000C000C00144Q000D5Q00202Q000D000D000D4Q000E5Q002054000E000E00182Q0095010A000E4Q005301093Q000100046D3Q004C00012Q00A4000700043Q001225010800194Q0012010900014Q007D0007000900012Q00A400076Q000201085Q00202Q00080008001800202Q00080008000500102Q0007001800084Q00075Q00202Q000700070018000E2Q001A00850001000700046D3Q008500012Q00A4000700043Q0012070108001B6Q0007000200014Q000700063Q00122Q0008001A6Q0007000200016Q00013Q00044Q008500010026803Q00850001001A00046D3Q008500010006B40004008500013Q00046D3Q008500012Q00A4000500053Q00205400050005001C0026800005006A0001001D00046D3Q006A00012Q00A4000500053Q00205400050005001E2Q0010000500053Q0006400105006C0001000100046D3Q006C00012Q00A4000500053Q00205400050005001E00205400060004000F0012860107001F3Q00202Q00070007001600122Q000800076Q000900053Q00122Q000A00076Q0007000A00024Q00060006000700122Q000700153Q00202Q0007000700164Q000800064Q00B80007000200020010160102001500072Q00A400075Q00300D0007000600202Q00A400075Q00300D0007001800072Q00A4000700043Q00126A0108000A3Q00205400080008000B001225010900214Q00A4000A5Q002054000A000A000D2Q00950108000A4Q005301073Q00012Q00A400055Q00125D010600223Q00202Q0006000600234Q00075Q00202Q00070007000D00202Q00070007000E4Q00060002000200102Q0005000D00066Q00017Q00213Q00030E3Q00537475636B446574656374696F6E03073Q00456E61626C6564030B3Q0043752Q72656E74526F636B03063Q00506172656E74030A3Q004C617374526F636B485000030B3Q004C617374526F636B52656603123Q004D696E657353696E636548504368616E6765028Q00030E3Q00537475636B436865636B54696D65030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D6503113Q00506F736974696F6E5468726573686F6C6403153Q00506F736974696F6E436865636B496E74657276616C03043Q007469636B03083Q00506F736974696F6E03093Q004D61676E697475646503103Q004C6173745265636F7665727954696D6503103Q005265636F76657279432Q6F6C646F776E03063Q00737472696E6703063Q00666F726D617403293Q00732C3F20535455434B20504F533A206D6F76656420252E3266203C20252E326620696E20252E316673026Q00F03F030D3Q005265636F766572794C6576656C030E3Q004C32412Q74656D7074436F756E74030D3Q0054696D655468726573686F6C64027Q0040024Q007E842E41030B3Q005468726573686F6C644C33026Q000840030B3Q005468726573686F6C644C32026Q00F83F030B3Q005468726573686F6C644C3100D74Q00A47Q0020545Q00010006B43Q000900013Q00046D3Q000900012Q00A47Q0020545Q00010020545Q0002000640012Q000A0001000100046D3Q000A00012Q00C43Q00014Q00A43Q00013Q0020545Q00030006B43Q001100013Q00046D3Q0011000100205400013Q00040006402Q01001E0001000100046D3Q001E00012Q00A4000100013Q0030620001000500064Q000100013Q00302Q0001000700064Q000100013Q00302Q0001000800094Q000100013Q00302Q0001000A00094Q000100013Q00302Q0001000B00064Q000100013Q00302Q0001000C00096Q00014Q00A4000100024Q00A80001000100024Q000200036Q000300016Q0002000200024Q00035Q00202Q00030003000100062Q0002005E00013Q00046D3Q005E000100205400040003000D0006B40004005E00013Q00046D3Q005E000100205400040003000E0006B40004005E00013Q00046D3Q005E000100126A0104000F4Q00110004000100022Q00A4000500013Q00205400050005000C000640010500340001000100046D3Q00340001001225010500094Q00D500050004000500205400060003000E0006B30006005E0001000500046D3Q005E00012Q00A4000500013Q00205400050005000B0006B40005005900013Q00046D3Q005900010020540005000200102Q00D2000600013Q00202Q00060006000B4Q00050005000600202Q00050005001100202Q00060003000D00062Q000500590001000600046D3Q005900012Q00A4000600013Q0020540006000600122Q00D50006000400060020540007000300130006B3000700590001000600046D3Q005900012Q00A4000600043Q00126A010700143Q002054000700070015001225010800164Q003C000900053Q002054000A0003000D002054000B0003000E2Q004C0007000B00022Q0012010800014Q007D0006000800012Q00A4000600053Q001225010700174Q009A0106000200012Q00A4000600013Q0010160106000A00042Q00A4000500013Q0020540006000200100010160105000B00062Q00A4000500013Q0010160105000C00042Q00A4000100064Q005801028Q00010002000200122Q0002000F6Q0002000100024Q000300013Q00202Q00030003000700062Q0003007800013Q00046D3Q007800012Q00A4000300013Q0010160103000500012Q00A4000300013Q001016010300074Q00A4000300013Q00300D0003000800092Q00A4000300013Q0010160103000A00022Q00A4000300013Q00300D0003001800092Q00A4000300013Q00300D0003001900092Q00A4000300013Q00300D0003000B00062Q00A4000300013Q0010160103000C00022Q00C43Q00013Q0006402Q01008A0001000100046D3Q008A00012Q00A4000300013Q00205400030003000A0006400103007F0001000100046D3Q007F00012Q003C000300024Q00D50003000200032Q00EB00045Q00202Q00040004000100202Q00040004001A00202Q00040004001B00062Q000400890001000300046D3Q008900012Q00A4000400053Q001225010500174Q009A0104000200012Q00C43Q00014Q00A4000300013Q0020540003000300050006400103008F0001000100046D3Q008F00010012250103001C3Q0006A32Q0100A20001000300046D3Q00A200012Q00A4000300013Q0010250003000500014Q000300013Q00302Q0003000800094Q000300013Q00102Q0003000A00024Q000300013Q00302Q0003001800094Q000300013Q00302Q00030019000900262Q000100A10001000900046D3Q00A100012Q00A4000300013Q00300D0003000500062Q00A4000300013Q00300D0003000700062Q00C43Q00014Q00A4000300014Q007F010400013Q00202Q00040004000800202Q00040004001700102Q0003000800044Q000300013Q00202Q00030003000A4Q0003000200034Q000400013Q00202Q0004000400124Q0004000200044Q00055Q00202Q00050005000100202Q00050005001300062Q000400B30001000500046D3Q00B300012Q00C43Q00014Q00A400045Q0020430104000400014Q000500013Q00202Q00050005000800202Q00060004001D00062Q000600BE0001000500046D3Q00BE00012Q00A4000500053Q0012250106001E4Q009A01050002000100046D3Q00D600012Q00A4000500013Q00205400050005000800205400060004001F00064B000600050001000500046D3Q00C7000100205400050004001A00205E0005000500200006B3000500CB0001000300046D3Q00CB00012Q00A4000500053Q0012250106001B4Q009A01050002000100046D3Q00D600012Q00A4000500013Q00205400050005000800205400060004002100064B000600040001000500046D3Q00D3000100205400050004001A0006B3000500D60001000300046D3Q00D600012Q00A4000500053Q001225010600174Q009A0105000200012Q00C43Q00017Q00093Q0003043Q007479706503063Q00737472696E6703053Q007461626C6503043Q005465787403073Q004D652Q7361676503073Q00436F6E74656E7403043Q007465787403073Q006D652Q7361676503073Q00636F6E74656E74011F3Q00126A2Q0100014Q003C00026Q00B8000100020002002680000100060001000200046D3Q000600012Q003A3Q00023Q00126A2Q0100014Q003C00026Q00B80001000200020026800001001C0001000300046D3Q001C000100205400013Q00040006402Q01001B0001000100046D3Q001B000100205400013Q00050006402Q01001B0001000100046D3Q001B000100205400013Q00060006402Q01001B0001000100046D3Q001B000100205400013Q00070006402Q01001B0001000100046D3Q001B000100205400013Q00080006402Q01001B0001000100046D3Q001B000100205400013Q00092Q003A000100024Q002C000100014Q003A000100024Q00C43Q00017Q00103Q0003053Q007063612Q6C03043Q006D6174682Q033Q006D696E026Q00F03F026Q00144003363Q002043612Q6E6F742066696E64204E6F74696669636174696F6E536572766963652E52452E4E6F74696679202D20726574727920696E2003013Q007303043Q007461736B03053Q0064656C61792Q033Q00497341030B3Q0052656D6F74654576656E74033E3Q00204E6F74696669636174696F6E536572766963652E4E6F74696679206973206E6F742052656D6F74654576656E74202D20682Q6F6B2064697361626C6564028Q00030D3Q004F6E436C69656E744576656E7403073Q00436F2Q6E65637403193Q00204E6F74696669636174696F6E20482Q6F6B2041435449564500444Q00A47Q0006B43Q000400013Q00046D3Q000400012Q00C43Q00013Q00126A012Q00013Q00066B2Q013Q000100012Q00A43Q00014Q00643Q000200010006B43Q000C00013Q00046D3Q000C00010006402Q0100230001000100046D3Q0023000100126A010200023Q0020540002000200032Q00A4000300023Q002034000300030004001225010400054Q004C0002000400022Q00D7000200024Q00A4000200024Q00A4000300033Q001225010400064Q003C000500023Q001225010600074Q007A0004000400062Q0012010500014Q007D00030005000100126A010300083Q0020540003000300092Q003C000400023Q00066B01050001000100022Q00A43Q00044Q00A43Q00054Q007D0003000500012Q00C43Q00013Q00203800020001000A0012250104000B4Q004C0002000400020006400102002D0001000100046D3Q002D00012Q00A4000200033Q0012250103000C4Q0012010400014Q007D0002000400012Q00C43Q00013Q0012250102000D4Q00D7000200023Q00205400020001000E00203800020002000F00066B010400020001000B2Q00A43Q00064Q00A43Q00074Q00A43Q00084Q00A43Q00044Q00A43Q00094Q00A43Q000A4Q00A43Q000B4Q00A43Q000C4Q00A43Q000D4Q00A43Q000E4Q00A43Q00034Q004D0002000400024Q00028Q000200033Q00122Q000300106Q000400016Q0002000400016Q00013Q00033Q00073Q0003063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q00536572766963657303133Q004E6F74696669636174696F6E5365727669636503023Q00524503063Q004E6F74696679000A4Q00A47Q0020545Q00010020545Q00020020545Q00030020545Q00040020545Q00050020545Q00060020545Q00072Q003A3Q00024Q00C43Q00017Q00013Q00030A3Q004175746F4D696E696E6700074Q00A47Q0020545Q00010006B43Q000600013Q00046D3Q000600012Q00A43Q00014Q008C3Q000100012Q00C43Q00017Q00183Q0003053Q006C6F77657203043Q006773756203043Q003C2E2D3E034Q0003043Q0066696E64030E3Q00616C7265616479206D696E696E6703043Q007469636B03153Q004C617374416C72656164794D696E696E6754696D65030B3Q0043752Q72656E74526F636B030A3Q004175746F4D696E696E6703083Q00506F736974696F6E03093Q004D61676E6974756465030C3Q0043752Q72656E745068617365026Q00104003083Q0044697374616E6365026Q002040027Q0040030C3Q00536B692Q706564526F636B73030D3Q0050656E64696E675377697463682Q0103073Q00556E6B6E6F776E03063Q00737472696E6703063Q00666F726D6174032E3Q0020414C5245414459204D494E494E47207C20526F636B3A202573207C2050656E64696E67207377697463683Q2E01614Q00A400016Q003C00026Q00B80001000200020006402Q0100060001000100046D3Q000600012Q00C43Q00013Q0020380002000100012Q00B8000200020002002038000200020002001225010400033Q001225010500044Q004C000200050002002038000300020005001225010500064Q004C000300050002000640010300120001000100046D3Q001200012Q00C43Q00013Q00126A010300074Q006B0003000100024Q000400013Q00202Q0004000400084Q0004000300044Q000500023Q00062Q0004001B0001000500046D3Q001B00012Q00C43Q00014Q00A4000400013Q0020540004000400090006B40004002300013Q00046D3Q002300012Q00A4000400033Q00205400040004000A000640010400240001000100046D3Q002400012Q00C43Q00014Q00A4000400044Q002A0104000100024Q000500056Q000600046Q0005000200024Q000600066Q000700013Q00202Q0007000700094Q00060002000200062Q0005003100013Q00046D3Q00310001000640010600320001000100046D3Q003200012Q00C43Q00013Q00205400070006000B00201400080005000B4Q00070007000800202Q00070007000C4Q000800013Q00202Q00080008000D00262Q0008003B0001000E00046D3Q003B00012Q00C43Q00014Q00A4000800033Q00205400080008000F0020340008000800100006A3010800410001000700046D3Q004100012Q00C43Q00014Q00A4000800074Q00D5000800030008000EA8011100460001000800046D3Q004600012Q00C43Q00014Q00A4000800013Q00105F0108000800034Q000800013Q00202Q0008000800124Q000900013Q00202Q0009000900094Q000A00086Q000A0003000A4Q00080009000A4Q000800013Q00302Q0008001300142Q00D9000800096Q000900013Q00202Q0009000900094Q00080002000200062Q000800580001000100046D3Q00580001001225010800154Q00A40009000A3Q001233000A00163Q00202Q000A000A001700122Q000B00186Q000C00086Q000A000C00024Q000B00016Q0009000B00016Q00017Q00033Q00030A3Q00446973636F2Q6E656374031F3Q00204E6F74696669636174696F6E20482Q6F6B20444953434F2Q4E4543544544029Q000E4Q00A47Q0006B43Q000B00013Q00046D3Q000B00012Q00A47Q002071014Q00016Q000200019Q009Q006Q00013Q00122Q000100028Q00020001001225012Q00034Q00D73Q00024Q00C43Q00017Q00103Q0003043Q007469636B03043Q006D6174682Q033Q006D617803093Q004D696E6544656C6179029A5Q99B93F029A5Q99A93F030F3Q004D696E6544656C61794A692Q746572028Q0003063Q0072616E646F6D026Q00F03F03063Q00737472696E6703063Q00666F726D617403183Q00204D696E6520232564202844656C61793A20252E3266732903053Q007063612Q6C03153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C003F3Q0012BB3Q00018Q0001000200122Q000100023Q00202Q0001000100034Q00025Q00202Q00020002000400062Q000200090001000100046D3Q00090001001225010200053Q001225010300064Q004C00010003000200126A010200023Q0020540002000200032Q00A400035Q002054000300030007000640010300120001000100046D3Q00120001001225010300083Q001225010400084Q004500020004000200122Q000300023Q00202Q0003000300094Q0003000100024Q0003000300024Q0003000100034Q000400016Q00043Q000400062Q0004001E0001000300046D3Q001E00012Q00C43Q00014Q00A4000400023Q00205501040004000A4Q000400028Q00016Q000400033Q00122Q0005000B3Q00202Q00050005000C00122Q0006000D6Q000700026Q000800036Q000500084Q005301043Q000100126A0104000E3Q00066B01053Q000100012Q00A43Q00044Q009A0104000200012Q00A4000400054Q00110004000100020006B40004003C00013Q00046D3Q003C000100203800050004000F001225010700104Q004C0005000700020006B40005003B00013Q00046D3Q003B000100126A0106000E3Q00066B01070001000100012Q003C3Q00054Q009A0106000200012Q001D00056Q00A4000500064Q008C0005000100012Q00C43Q00013Q00023Q00093Q0003063Q0053686172656403083Q005061636B6167657303043Q004B6E697403083Q005365727669636573030B3Q00542Q6F6C5365727669636503023Q005246030D3Q00542Q6F6C416374697661746564030C3Q00496E766F6B6553657276657203073Q005069636B617865000C4Q005E016Q00206Q000100206Q000200206Q000300206Q000400206Q000500202Q00013Q000600202Q00010001000700202Q00010001000800122Q000300094Q007D0001000300012Q00C43Q00017Q00013Q0003083Q00416374697661746500044Q00A47Q0020385Q00012Q009A012Q000200012Q00C43Q00017Q000A3Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C030E3Q0046696E6446697273744368696C6403083Q004261636B7061636B03053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103083Q0048756D616E6F696403093Q004571756970542Q6F6C002D4Q00A48Q00113Q00010002000640012Q00050001000100046D3Q000500012Q00C43Q00013Q00205400013Q00010006B40001000D00013Q00046D3Q000D0001002038000200010002001225010400034Q004C0002000400020006B40002000E00013Q00046D3Q000E00012Q00C43Q00013Q00203800023Q0004001225010400054Q004C000200040002000640010200140001000100046D3Q0014000100205400023Q0005000640010200170001000100046D3Q001700012Q00C43Q00013Q00126A010300063Q0020380004000200072Q0030000400054Q002300033Q000500046D3Q002A0001002038000800070008001225010A00034Q004C0008000A00020006B40008002A00013Q00046D3Q002A0001002038000800010004001225010A00094Q004C0008000A00020006B40008002900013Q00046D3Q0029000100203800090008000A2Q003C000B00074Q007D0009000B00012Q00C43Q00013Q0006770103001C0001000200046D3Q001C00012Q00C43Q00017Q00163Q00032F3Q00204D616769632043617270657420616C7265616479206578697374732C20736B692Q70696E67206372656174696F6E03083Q00496E7374616E63652Q033Q006E657703043Q005061727403043Q004E616D6503113Q004D696E696E674D6167696343617270657403043Q0053697A6503073Q00566563746F7233026Q001840026Q00E03F030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C696465010003083Q0043616E546F75636803083Q0043616E517565727903063Q00506172656E74034A3Q00204D61676963204361727065742043524541544544207C2053697A653A203678302E357836207C20416E63686F7265643A2074727565207C2043616E436F2Q6C6964653A2066616C736503053Q007072696E74032C3Q005B466F726765204D696E696E675D204D61676963204361727065742043726561746564202853746174696329002B4Q00A47Q0006B43Q000700013Q00046D3Q000700012Q00A43Q00013Q0012252Q0100014Q009A012Q000200012Q00C43Q00013Q00126A012Q00023Q0020485Q000300122Q000100048Q000200029Q009Q0000304Q000500069Q0000122Q000100083Q00202Q00010001000300122Q000200093Q0012250103000A3Q001225010400094Q004C000100040002001016012Q000700012Q0049016Q00304Q000B000C9Q0000304Q000D000E9Q0000304Q000F00109Q0000304Q001100109Q0000304Q001200102Q00A48Q00A4000100023Q001016012Q001300012Q00283Q00013Q00122Q000100146Q000200018Q0002000100124Q00153Q00122Q000100168Q000200016Q00017Q00123Q0003063Q00434672616D652Q033Q006E6577028Q00030B3Q0047686F73744F2Q6673657403063Q00506172656E7403083Q0043616E546F75636803083Q0043616E5175657279010003043Q006D61746803063Q0072616E646F6D027B14AE47E17A943F03083Q00506F736974696F6E03063Q00737472696E6703063Q00666F726D617403373Q004D616769632043617270657420757064617465643A2028252E31662C20252E31662C20252E316629207C204F2Q667365743A20252E316603013Q005803013Q005903013Q005A01393Q000640012Q00030001000100046D3Q000300012Q00C43Q00014Q00A400015Q0006402Q0100080001000100046D3Q000800012Q00A4000100014Q008C00010001000100205400013Q0001001244000200013Q00202Q00020002000200122Q000300036Q000400023Q00202Q00040004000400122Q000500036Q0002000500024Q0001000100024Q00025Q00202Q0002000200054Q000300033Q00062Q000200190001000300046D3Q001900012Q00A400026Q00A4000300033Q0010160102000500032Q00A400025Q002054000200020006000640010200210001000100046D3Q002100012Q00A400025Q0020540002000200070006B40002002500013Q00046D3Q002500012Q00A400025Q00300D0002000600082Q00A400025Q00300D0002000700082Q00A400025Q00100B00020001000100122Q000200093Q00202Q00020002000A4Q00020001000200262Q000200380001000B00046D3Q0038000100205400020001000C2Q00A4000300043Q00126A0104000D3Q00205400040004000E0012250105000F3Q0020540006000200100020540007000200110020540008000200122Q00A4000900023Q0020540009000900042Q0095010400094Q005301033Q00012Q00C43Q00017Q00043Q0003073Q0044657374726F7903163Q004D61676963204361727065742044455354524F59454403053Q007072696E7403253Q005B466F726765204D696E696E675D204D61676963204361727065742044657374726F79656400104Q00A47Q0006B43Q000F00013Q00046D3Q000F00012Q00A47Q002082014Q00016Q000200019Q009Q006Q00013Q00122Q000100026Q000200018Q0002000100124Q00033Q00122Q000100044Q009A012Q000200012Q00C43Q00017Q00143Q0003163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030D3Q00506C6174666F726D5374616E64010003043Q004865616403053Q00546F72736F030A3Q00552Q706572546F72736F030A3Q004C6F776572546F72736F03053Q0070616972732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964652Q0103053Q007072696E7403463Q005B4D696E696E675D20436C65616E7570506879736963733A20506C6174666F726D5374616E643D66616C73652C2043616E436F2Q6C6964653D7472756520726573746F72656403073Q0044657374726F79003B4Q00A48Q00113Q000100020006B43Q003200013Q00046D3Q003200012Q00A4000100014Q003C00026Q00B80001000200020006B40001000F00013Q00046D3Q000F000100126A010200023Q00203900020002000300102Q00010001000200122Q000200023Q00202Q00020002000300102Q00010004000200203800023Q0005001225010400064Q004C0002000400020006B40002001800013Q00046D3Q001800010020540003000200070006B40003001800013Q00046D3Q0018000100300D0002000700082Q0046000300043Q001272000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q0007000C6Q00030004000100126A0104000D4Q003C000500034Q006400040002000600046D3Q002D000100203800093Q00052Q003C000B00084Q004C0009000B00020006B40009002D00013Q00046D3Q002D0001002038000A0009000E001225010C000F4Q004C000A000C00020006B4000A002D00013Q00046D3Q002D000100300D000900100011000677010400220001000200046D3Q0022000100126A010400123Q001225010500134Q009A0104000200012Q00A4000100023Q0006B40001003A00013Q00046D3Q003A00012Q00A4000100023Q0020380001000100142Q009A2Q01000200012Q002C000100014Q00D7000100024Q00C43Q00017Q00033Q0003073Q0044657374726F79030A3Q00446973636F2Q6E65637403163Q002046752Q6C20436C65616E757020436F6D706C65746500394Q0046019Q002Q000100016Q00018Q000100016Q00023Q00064Q000C00013Q00046D3Q000C00012Q00A43Q00023Q0020385Q00012Q009A012Q000200012Q002C8Q00D73Q00024Q00A43Q00033Q0006B43Q001400013Q00046D3Q001400012Q00A43Q00033Q0020385Q00022Q009A012Q000200012Q002C8Q00D73Q00034Q00A43Q00043Q0006B43Q001C00013Q00046D3Q001C00012Q00A43Q00043Q0020385Q00022Q009A012Q000200012Q002C8Q00D73Q00044Q00A43Q00054Q00A4000100064Q00B83Q000200020006B43Q002600013Q00046D3Q002600012Q00A43Q00063Q0020385Q00022Q009A012Q000200012Q002C8Q00D73Q00064Q00A43Q00054Q00A4000100074Q00B83Q000200020006B43Q003000013Q00046D3Q003000012Q00A43Q00073Q0020385Q00022Q009A012Q000200012Q002C8Q00D73Q00074Q0012017Q00953Q00088Q00098Q000100016Q000A3Q00122Q000100036Q000200018Q000200016Q00017Q00193Q0003123Q004D61696E74656E616E6365456E61626C656403043Q007469636B03103Q0053652Q73696F6E537461727454696D65028Q0003133Q004C6173744D61696E74656E616E636554696D6503133Q004D61696E74656E616E6365496E74657276616C03183Q004D61696E74656E616E63654D696E655468726573686F6C64024Q008087C34003103Q004D61696E74656E616E6365436F756E74026Q00F03F03063Q00737472696E6703063Q00666F726D617403293Q00204D41494E54454E414E434520232564207C20557074696D653A202573207C204D696E65643A202564030A3Q00546F74616C4D696E6564030E3Q004C6173744C2Q6F6B54617267657400030D3Q0050656E64696E67537769746368010003113Q004C61737450656E64696E67537769746368030C3Q00536B692Q706564526F636B7303063Q006763696E666F026Q004E4003163Q00204D616769634361727065742052454652455348454403073Q0044657374726F7903483Q00204D61696E74656E616E636520436F6D706C657465207C204D696E65732072657365743A2025642D3E30207C204D656D6F72793A20252E3166204B42207C204D504D3A20252E316600724Q00A47Q0020545Q0001000640012Q00050001000100046D3Q000500012Q00C43Q00013Q00126A012Q00024Q00113Q000100022Q00A4000100013Q0020540001000100030026800001000C0001000400046D3Q000C00012Q00C43Q00014Q00A4000100013Q0020540001000100052Q00D500013Q00012Q00A400025Q00205400020002000600064B000200020001000100046D3Q001400012Q00132Q016Q00122Q0100014Q00A4000200024Q00A400035Q0020540003000300070006400103001B0001000100046D3Q001B0001001225010300083Q00064B000300020001000200046D3Q001E00012Q001301026Q0012010200013Q0006402Q0100240001000100046D3Q00240001000640010200240001000100046D3Q002400012Q00C43Q00014Q00A4000300014Q008A010400013Q00202Q00040004000900202Q00040004000A00102Q0003000900044Q000300013Q00102Q000300056Q000300036Q000400013Q00202Q0004000400034Q00043Q00044Q0003000200024Q000400043Q00122Q0005000B3Q00202Q00050005000C00122Q0006000D6Q000700013Q00202Q0007000700094Q000800036Q000900013Q00202Q00090009000E4Q0005000900024Q000600016Q0004000600014Q000400023Q00122Q000500046Q000500026Q000500013Q00302Q0005000F00104Q000500013Q00302Q0005001100124Q000500013Q00302Q0005001300044Q000500016Q00065Q00102Q00050014000600122Q000500156Q00050001000200122Q000600046Q000700013Q00202Q000700070003000E2Q000400580001000700046D3Q005800012Q00A4000700013Q0020540007000700032Q00D500073Q00070020F7000700070016000EA8010400580001000700046D3Q005800012Q00A4000800013Q00205400080008000E2Q00A90006000800072Q00A4000700054Q00BA0007000100014Q000700066Q0007000100014Q000700043Q00122Q000800176Q0007000200014Q000700073Q00062Q0007006700013Q00046D3Q006700012Q00A4000700073Q0020380007000700182Q009A0107000200012Q002C000700074Q00D7000700074Q00A4000700043Q0012A20008000B3Q00202Q00080008000C00122Q000900196Q000A00046Q000B00056Q000C00066Q0008000C00024Q000900016Q0007000900016Q00017Q000A3Q0003063Q0048656967687403083Q00506F736974696F6E030A3Q00466C696768744D6F646503053Q0041626F766503013Q0059025Q00207CC003073Q00566563746F72332Q033Q006E657703013Q005803013Q005A01184Q008F00015Q00202Q00010001000100202Q00023Q00024Q000300036Q00045Q00202Q00040004000300262Q0004000B0001000400046D3Q000B00010020540004000200052Q00E900030004000100046D3Q000D00010020540004000200052Q00D5000300040001002632010300100001000600046D3Q00100001001225010300063Q00126A010400073Q0020540004000400080020540005000200092Q003C000600033Q00205400070002000A2Q00FF000400074Q002D00046Q00C43Q00017Q007B3Q0003083Q00506F736974696F6E03243Q0020504F534954494F4E204953204E614E212041626F7274696E67206D6F76656D656E742E03103Q00486F72697A6F6E74616C4F2Q6673657403043Q006D6174682Q033Q00616273028Q0003073Q00566563746F72332Q033Q006E657703013Q005803013Q005A03093Q004D61676E6974756465023Q00E04D62503F03043Q00556E6974030A3Q0047686F737453702Q6564026Q11913F030C3Q0043752Q72656E745068617365027Q0040026Q000840026Q001040026Q00344003133Q00446972656374436861736544697374616E636503013Q0059026Q001440026Q00F03F030D3Q00506C6174666F726D5374616E642Q0102CD5QCCF43F03063Q00737472696E6703063Q00666F726D617403313Q0020444952454354204348415345207C20646973743A252E3166203C202564207C20736B692Q70696E672050686173652031026Q002440026Q003E40034Q00030F3Q0050313A4845494748545F434845434B030C3Q0050323A524F434B5F474F4E4503123Q0020526F636B206D6F7665642120666C61743D03053Q00666C2Q6F72030A3Q002Q2043686173696E672103123Q0050333A485953544552455349535F4C4F434B026Q002E4003113Q0050343A4E4F545F504F534954494F4E4544030D3Q0050353A564552595F434C4F5345030F3Q0050353A4E4F524D414C5F454E545259030E3Q0050353A4B2Q45505F4445504C4F5903063Q0072616E646F6D029A5Q99A93F03013Q004E03323Q00205048415345207C2025642564207C20666C61743A252E316620646973743A252E3166207C20776173343A2573207C20257303163Q00412Q73656D626C794C696E65617256656C6F6369747903043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q004C6F636B65644D696E65506F7300030D3Q0053702Q6564412Q70726F616368030E3Q00536B69704D696E654672616D657303083Q0044697374616E6365030F3Q004F7265436865636B456E61626C6564030B3Q0043752Q72656E74526F636B03073Q00556E6B6E6F776E03103Q004C61737446696C746572536F75726365030E3Q004C61737446696C746572526F636B032F3Q00204F52452046494C54455220534F55524345207C202573207C205573696E672025732066696C7465723A205B25735D03053Q007461626C6503063Q00636F6E63617403023Q002C20030D3Q004F7265436865636B4C6576656C030F3Q004F7265536B69704E6F74696669656403043Q007469636B2Q033Q006E696C03343Q00204F524520434845434B207C20526F636B3A202573207C204C6576656C3A2025642Q25207C20412Q4C204F7265733A205B25735D03063Q0069706169727303083Q00746F737472696E6703053Q006C6F77657203363Q002046494C54455220434845434B207C204F7265733A205B25735D2076732046696C7465723A205B25735D207C204D617463683A20257303063Q00594553202D2003013Q003F03023Q004E4F030C3Q00536B692Q706564526F636B7303133Q004F726520536B697020284D69736D6174636829034D3Q0020534B495020524F434B207C202725732720686173206F726573205B25735D206275742066696C7465722077616E7473205B25735D207C204C6576656C3A2025642Q25207C2043443A20256473033D3Q00204F5245204D41544348207C20526F636B202725732720686173205B25735D207C204D6174636865643A2027257327207C204C6576656C3A2025642Q25030C3Q004D617463686564526F636B73030D3Q004F7265536B69704E6F74696679032B3Q00E29C8520257320402025642Q250AF09F928E204861733A2025730AF09F8EAF204D6174636865643A20257303053Q005469746C65030E3Q00E29C85204F7265204D617463682103073Q00436F6E74656E7403083Q004475726174696F6E026Q00204003113Q004F726520536B697020284E6F204F726529033C3Q00204F5245204E494C207C20526F636B20272573272061742025642Q2520686173206E6F204F726520612Q7472696275746521207C2043443A20256473027B14AE47E17A943F03313Q0020542Q4F2046415220544F204D494E45207C20646973743A252E3166203E20436F6E6669672E44697374616E63653A256402B81E85EB51B89E3F030D3Q0053616665747920417363656E74030A3Q00536B7920437275697365030A3Q004465706C6F796D656E7403063Q004D696E696E67032A3Q002050686173652025643A202573207C20446973743A20252E3166207C20593A20252E31662Q20252E3166029A5Q99B93F03093Q0053702Q65644E656172030B3Q0053702Q6564536C6F776D6F026Q00494003083Q0053702Q65644661722Q033Q006D696E03083Q00496E7374616E636503083Q00426F64794779726F03093Q004D6178546F72717565024Q00652QCD4103013Q0050025Q0088C34003013Q0044026Q00594003063Q00506172656E7403143Q004C61737454726176656C4C2Q6F6B546172676574030E3Q004C6173744C2Q6F6B54617267657403103Q00526F746174696F6E446561645A6F6E6503063Q00434672616D6503063Q006C2Q6F6B4174030A3Q004C2Q6F6B566563746F7203453Q0020524F544154494F4E207C2046752Q6C334420617420726F636B207C20446973743A20252E3166207C204C2Q6F6B5665633A2028252E32662C20252E32662C20252E32662903043Q006875676503163Q00526F746174696F6E446561645A6F6E6554726176656C044D033Q001801048Q00058Q00040002000100202Q00043Q000100202Q0005000200010002BC00066Q003C000700064Q003C000800044Q00B80007000200020006B40007001000013Q00046D3Q001000012Q003C000700064Q003C000800054Q00B8000700020002000640010700150001000100046D3Q001500012Q00A4000700013Q001225010800024Q0012010900014Q007D0007000900012Q00C43Q00014Q00A4000700024Q00BE000800026Q0007000200024Q000800036Q000900046Q0008000200024Q000900043Q00202Q00090009000300062Q0009003F00013Q00046D3Q003F000100126A010900043Q0020060109000900054Q000A00043Q00202Q000A000A00034Q000900020002000E2Q0006003F0001000900046D3Q003F000100126A010900073Q00206600090009000800202Q000A0005000900202Q000B000400094Q000A000A000B00122Q000B00063Q00202Q000C0005000A00202Q000D0004000A4Q000C000C000D4Q0009000C000200202Q000A0009000B000E2Q000C003F0001000A00046D3Q003F0001002054000A0009000D00126F000B00073Q00202Q000B000B000800202Q000C000A000A4Q000C000C3Q00122Q000D00063Q00202Q000E000A00094Q000B000E00024Q000C00043Q00202Q000C000C00034Q000C000B000C4Q00070007000C2Q00A4000900043Q00205400090009000E000639010A00440001000300046D3Q00440001001225010A000F4Q005701090009000A00127B010A00073Q00202Q000A000A000800202Q000B0007000900202Q000C000400094Q000B000B000C00122Q000C00063Q00202Q000D0007000A00202Q000E0004000A4Q000D000D000E4Q000A000D000200202Q000A000A000B4Q000B0007000400202Q000B000B000B4Q000C000C6Q000D5Q00122Q000E00066Q000F00053Q00202Q000F000F001000262Q000F005A0001001100046D3Q005A00012Q0013010F6Q0012010F00014Q00A4001000053Q0020540010001000100026A7011000640001001200046D3Q006400012Q00A4001000053Q0020540010001000100026A7011000640001001300046D3Q006400012Q001301106Q0012011000013Q0006B40010006C00013Q00046D3Q006C0001000EA80114006C0001000A00046D3Q006C00012Q001201106Q00A4001100053Q00300D0011001000062Q00A4001100043Q00205400110011001500064B000B00020001001100046D3Q007100012Q001301116Q0012011100013Q0006400111008A0001000100046D3Q008A0001000640010F008A0001000100046D3Q008A00010006400110008A0001000100046D3Q008A00010020540012000400160020340113000800170006A30112008A0001001300046D3Q008A0001001225010E00183Q0012BD001200073Q00202Q00120012000800202Q0013000400094Q001400083Q00202Q00150004000A4Q0012001500024Q000C00123Q00202Q00120001001900062Q001200880001000100046D3Q0088000100300D00010019001A00205E00090009001B00046D3Q007902010006B4001100A400013Q00046D3Q00A40001000640010F00A40001000100046D3Q00A40001000640011000A40001000100046D3Q00A400010020540012000400160020340113000800170006A3011200A40001001300046D3Q00A40001001225010E00124Q003C000C00073Q0020540012000100190006400112009A0001000100046D3Q009A000100300D00010019001A2Q00A4001200013Q0012750113001C3Q00202Q00130013001D00122Q0014001E6Q0015000B6Q001600043Q00202Q0016001600154Q001300166Q00123Q000100044Q00790201000640010F00AA0001000100046D3Q00AA00010020540012000400160020340113000800170006B3001300C50001001200046D3Q00C50001000EA8011F00C50001000A00046D3Q00C50001000640011000C50001000100046D3Q00C50001001225010E00114Q003C001200083Q0020540013000400160020340114000800170006A3011300B50001001400046D3Q00B5000100203400120008001100126A011300073Q00208701130013000800202Q0014000700094Q001500123Q00202Q00160007000A4Q0013001600024Q000C00133Q00262Q000A00BF0001002000046D3Q00BF00012Q0013010D6Q0012010D00013Q002054001300010019000640011300790201000100046D3Q0079020100300D00010019001A00046D3Q007902012Q00A4001200053Q0020540012001200100026A7011200CA0001001300046D3Q00CA00012Q001301126Q0012011200013Q00126A011300043Q0020540013001300050020540014000400160020540015000700162Q00D50014001400152Q00B8001300020002001225011400133Q001225011500213Q00205400160004001600205400170007001600203401170017001F0006D4001600DE0001001700046D3Q00DE000100205400160004001600205400170007001600203400170017001F0006D4001700DE0001001600046D3Q00DE00012Q001301166Q0012011600013Q0006B4001600E400013Q00046D3Q00E40001001225010E00123Q001225011500223Q00046D3Q00132Q010006B4001200F500013Q00046D3Q00F50001000EA8011F00F50001000A00046D3Q00F50001001225010E00183Q001283001500236Q001700013Q00122Q001800243Q00122Q001900043Q00202Q0019001900254Q001A000A6Q00190002000200122Q001A00266Q00180018001A4Q001900016Q00170019000100044Q00132Q010006B4001200FC00013Q00046D3Q00FC00010026D8000A00FC0001001F00046D3Q00FC0001001225010E00133Q001225011500273Q00046D3Q00132Q01000EA8012800032Q01000A00046D3Q00032Q01000640011200032Q01000100046D3Q00032Q01001225010E00123Q001225011500293Q00046D3Q00132Q01002632010A00082Q01001800046D3Q00082Q01001225010E00133Q0012250115002A3Q00046D3Q00132Q010006B4001000112Q013Q00046D3Q00112Q01002632010A00112Q01001700046D3Q00112Q010006A3010B00112Q01001400046D3Q00112Q01001225010E00133Q0012250115002B3Q00046D3Q00132Q01001225010E00123Q0012250115002C4Q00A4001700053Q002054001700170010000668000E001C2Q01001700046D3Q001C2Q0100126A011700043Q00205400170017002D2Q00110017000100020026320117002F2Q01002E00046D3Q002F2Q010006B4001200212Q013Q00046D3Q00212Q01001225011700163Q000640011700222Q01000100046D3Q00222Q010012250117002F4Q00A4001800013Q0012650019001C3Q00202Q00190019001D00122Q001A00306Q001B00053Q00202Q001B001B00104Q001C000E6Q001D000A6Q001E000B6Q001F00176Q002000156Q001900206Q00183Q0001002680000E00730201001300046D3Q0073020100126A011700073Q00203900170017003200104Q0031001700122Q001700073Q00202Q00170017003200104Q00330017002632010B00422Q01001100046D3Q00422Q012Q00A4001700053Q0020540017001700340006400117003F2Q01000100046D3Q003F2Q012Q00A4001700053Q0010160117003400042Q00A4001700053Q002054000C0017003400046D3Q00482Q012Q00A4001700053Q0030820017003400354Q000C00076Q001700043Q00202Q0017001700364Q0009000900170020540017000100190006400117004C2Q01000100046D3Q004C2Q0100300D00010019001A2Q00A4001700053Q002054001700170037000EA8010600562Q01001700046D3Q00562Q012Q00A4001700054Q00A4001800053Q00205400180018003700203401180018001800101601170037001800046D3Q007802012Q00A4001700043Q0020540017001700380020340017001700130006B3000B00640201001700046D3Q006402012Q00A4001700043Q0020540017001700390006B40017006102013Q00046D3Q006102012Q00A4001700053Q00205400170017003A0006B40017006102013Q00046D3Q006102012Q00A4001800064Q003C001900174Q00B8001800020002000640011800692Q01000100046D3Q00692Q010012250118003B4Q00A4001900074Q003C001A00184Q006400190002001A0006B4001A008A2Q013Q00046D3Q008A2Q012Q00A4001B00053Q002054001B001B003C000668001B00762Q01001A00046D3Q00762Q012Q00A4001B00053Q002054001B001B003D000659001B008A2Q01001800046D3Q008A2Q012Q00A4001B00053Q00109B001B003C001A4Q001B00053Q00102Q001B003D00184Q001B00013Q00122Q001C001C3Q00202Q001C001C001D00122Q001D003E6Q001E00186Q001F001A3Q00122Q0020003F3Q00202Q0020002000404Q002100193Q00122Q002200416Q002000226Q001C8Q001B3Q00014Q001B00086Q001C00186Q001B000200010006B40019006102013Q00046D3Q006102012Q002E011B00193Q000EA8010600610201001B00046D3Q006102012Q00A4001B00094Q003C001C00174Q00B8001B000200022Q00A4001C00043Q002054001C001C00420006B3001B00610201001C00046D3Q006102012Q00A4001C00053Q002054001C001C00432Q00A6001C001C0017000640011C00610201000100046D3Q006102012Q00A4001C00053Q00209E011C001C004300122Q001D00446Q001D000100024Q001C0017001D4Q001C000A6Q001D00176Q001C000200024Q001D001C3Q000E2Q000600AD2Q01001D00046D3Q00AD2Q0100126A011D003F3Q002051011D001D00404Q001E001C3Q00122Q001F00416Q001D001F000200062Q001D00AE2Q01000100046D3Q00AE2Q01001225011D00454Q00A4001E00013Q00121E001F001C3Q00202Q001F001F001D00122Q002000466Q002100186Q0022001B6Q0023001D6Q001F00236Q001E3Q00014Q001E001C3Q000E2Q0006003E0201001E00046D3Q003E02012Q0012011E6Q00F6001F001F3Q00122Q002000476Q0021001C6Q00200002002200044Q00D82Q0100126A012500484Q003C002600244Q00B80025000200020020380025002500492Q00B800250002000200126A012600474Q003C002700194Q006400260002002800046D3Q00D32Q0100126A012B00484Q0080012C002A6Q002B0002000200202Q002B002B00494Q002B0002000200062Q002500D32Q01002B00046D3Q00D32Q012Q0012011E00014Q003C001F00243Q00046D3Q00D52Q01000677012600C92Q01000200046D3Q00C92Q010006B4001E00D82Q013Q00046D3Q00D82Q0100046D3Q00DA2Q01000677012000C02Q01000200046D3Q00C02Q0100126A0120003F3Q0020210020002000404Q002100193Q00122Q002200416Q0020002200024Q002100013Q00122Q0022001C3Q00202Q00220022001D00122Q0023004A6Q0024001D6Q002500203Q00062Q001E00EE2Q013Q00046D3Q00EE2Q010012250126004B3Q000639012700EB2Q01001F00046D3Q00EB2Q010012250127004C4Q007A002600260027000640012600EF2Q01000100046D3Q00EF2Q010012250126004D4Q0095012200264Q005301213Q0001000640011E00140201000100046D3Q00140201001225012100064Q0030012200053Q00202Q00220022004E00202Q00220017001A4Q0022000B3Q00122Q0023004F6Q002400186Q0025001B6Q0026001D6Q002700206Q002800214Q003C002900174Q0059012A000E6Q0022002A00014Q002200013Q00122Q0023001C3Q00202Q00230023001D00122Q002400506Q002500186Q0026001D6Q002700206Q0028001B4Q003C002900214Q0095012300294Q005301223Q00012Q00A4002200053Q00300D0022003A00352Q00A4002200053Q00300D0022001000062Q00A4002200053Q00300D0022003400352Q00C43Q00013Q00046D3Q006102012Q00A4002100013Q0012710022001C3Q00202Q00220022001D00122Q002300516Q002400186Q0025001D3Q00062Q0026001D0201001F00046D3Q001D02010012250126004C4Q003C0027001B4Q0045012200276Q00213Q00014Q002100053Q00202Q00210021005200202Q00210017001A4Q002100043Q00202Q00210021005300062Q0021006102013Q00046D3Q006102012Q00A40021000C4Q003C002200174Q003C0023000E4Q004C0021002300020006B40021006102013Q00046D3Q0061020100126A0121001C3Q00205400210021001D001225012200544Q003C002300184Q003C0024001B4Q003C0025001D3Q000639012600360201001F00046D3Q003602010012250126004C4Q004C0021002600022Q00CC0022000D6Q00233Q000300302Q00230055005600102Q00230057002100302Q0023005800594Q00220002000100044Q00610201001225011E00064Q000E001F00053Q00202Q001F001F004E00202Q001F0017001A00122Q001F003F3Q00202Q001F001F00404Q002000193Q00122Q002100416Q001F002100024Q0020000B3Q00122Q0021005A6Q002200186Q0023001B6Q0024001D6Q0025001F6Q0026001E6Q002700176Q0028000E6Q0020002800014Q002000013Q00122Q0021001C3Q00202Q00210021001D00122Q0022005B6Q002300186Q0024001B6Q0025001E6Q002100256Q00203Q00014Q002000053Q00302Q0020003A00354Q002000053Q00302Q0020001000064Q002000053Q00302Q0020003400356Q00014Q00A40017000E4Q008C00170001000100046D3Q0078020100126A011700043Q00205400170017002D2Q0011001700010002002632011700780201005C00046D3Q007802012Q00A4001700013Q0012750118001C3Q00202Q00180018001D00122Q0019005D6Q001A000B6Q001B00043Q00202Q001B001B00384Q0018001B6Q00173Q000100044Q007802012Q003C000C00073Q002054001700010019000640011700780201000100046D3Q0078020100300D00010019001A2Q0012010D00014Q00A4001200053Q00100B00120010000E00122Q001200043Q00202Q00120012002D4Q00120001000200262Q001200950201005E00046D3Q009502012Q0046001200043Q0012720013005F3Q00122Q001400603Q00122Q001500613Q00122Q001600626Q0012000400012Q00A600130012000E0006400113008A0201000100046D3Q008A02010012250113003B4Q00A4001400013Q00126A0115001C3Q00205400150015001D001225011600634Q003C0017000E4Q003C001800134Q003C0019000B3Q002054001A00040016002054001B000700162Q00950115001B4Q005301143Q0001000640010C00980201000100046D3Q009802012Q00C43Q00014Q00D50012000C000400205400130012000B000EA80164009E0201001300046D3Q009E020100205400120012000D00046D3Q009F02012Q00C43Q00013Q0006B4000D00AB02013Q00046D3Q00AB0201002632011300A70201002800046D3Q00A702012Q00A4001400043Q0020540014001400652Q005701090009001400046D3Q00B002012Q00A4001400043Q0020540014001400662Q005701090009001400046D3Q00B00201000EA8016700B00201001300046D3Q00B002012Q00A4001400043Q0020540014001400682Q005701090009001400126A011400043Q0020900114001400694Q001500096Q001600136Q0014001600024Q000900146Q0014001200094Q0014000400144Q0015000F3Q00062Q001500CE0201000100046D3Q00CE020100126A0115006A3Q00203B01150015000800122Q0016006B6Q0015000200024Q0015000F6Q0015000F3Q00122Q001600073Q00202Q00160016000800122Q0017006D3Q00122Q0018006D3Q00122Q0019006D4Q004C0016001900020010610015006C00164Q0015000F3Q00302Q0015006E006F4Q0015000F3Q00302Q0015007000714Q0015000F3Q00102Q001500723Q002680000E000F0301001300046D3Q000F03012Q00A4001500053Q0030F30015007300354Q0015000F3Q00122Q001600073Q00202Q00160016003200102Q0015006C00164Q0015000F3Q00302Q0015006E00064Q00150005001400202Q00150015000B000E2Q006400090301001500046D3Q000903012Q00A4001600053Q002054001600160074000640011600E10201000100046D3Q00E102012Q003C001600054Q00D50017000500160020B600170017000B4Q001800186Q001900043Q00202Q00190019007500062Q001900EC0201001700046D3Q00EC02012Q00A4001900053Q002054001900190074000640011900F00201000100046D3Q00F002012Q00A4001900053Q0010160119007400052Q003C001800053Q00046D3Q00F102012Q003C001800163Q00126A011900763Q0020540019001900772Q003C001A00144Q003C001B00184Q004C0019001B000200100B3Q0076001900122Q001900043Q00202Q00190019002D4Q00190001000200262Q001900460301002E00046D3Q0046030100205400193Q007600207C0019001900784Q001A00013Q00122Q001B001C3Q00202Q001B001B001D00122Q001C00796Q001D00153Q00202Q001E0019000900202Q001F0019001600202Q00200019000A4Q001B00204Q0053011A3Q000100046D3Q0046030100126A011600763Q0020E50016001600084Q001700146Q00160002000200104Q0076001600044Q0046030100126A011500073Q00203E01150015000800202Q0016000C000900202Q00170014001600202Q0018000C000A4Q0015001800024Q00160015001400202Q00160016000B000E2Q006400350301001600046D3Q003503012Q00A4001700053Q0020540017001700730006B40017002303013Q00046D3Q002303012Q00A4001700053Q0020540017001700732Q00D500170015001700205400170017000B000640011700250301000100046D3Q0025030100126A011700043Q00205400170017007A2Q00A4001800043Q00205400180018007B0006400118002A0301000100046D3Q002A0301001225011800063Q0006A3011800350301001700046D3Q003503012Q00A40018000F3Q001285001900763Q00202Q0019001900774Q001A00146Q001B00156Q0019001B000200102Q0018007600194Q001800053Q00102Q0018007300152Q00A40017000F3Q0030600017006E006F4Q0017000F3Q00302Q0017007000714Q0017000F3Q00122Q001800073Q00202Q00180018000800122Q0019006D3Q00122Q001A006D3Q00122Q001B006D6Q0018001B000200102Q0017006C001800122Q001700763Q00202Q0017001700084Q001800146Q00170002000200104Q0076001700126A011500073Q0020A300150015003200104Q0031001500122Q001500073Q00202Q00150015003200104Q003300156Q00013Q00013Q00033Q0003013Q005803013Q005903013Q005A01103Q00205400013Q000100205400023Q00010006680001000C0001000200046D3Q000C000100205400013Q000200205400023Q00020006680001000C0001000200046D3Q000C000100205400013Q000300205400023Q00030006590001000D0001000200046D3Q000D00012Q00132Q016Q00122Q0100014Q003A000100024Q00C43Q00017Q000A3Q00030A3Q00446973636F2Q6E65637403073Q0044657374726F79030B3Q0043752Q72656E74526F636B00028Q00030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D6503143Q00204D696E696E67204C2Q6F702053544F2Q50454403053Q007072696E7403303Q005B466F726765204D696E696E675D204D696E696E672053746F2Q706564202D20436C65616E757020436F6D706C65746500324Q00A47Q0006B43Q000800013Q00046D3Q000800012Q00A47Q0020385Q00012Q009A012Q000200012Q002C8Q00D78Q00A43Q00013Q0006B43Q001000013Q00046D3Q001000012Q00A43Q00013Q0020385Q00012Q009A012Q000200012Q002C8Q00D73Q00014Q00A43Q00024Q00A13Q000100016Q00038Q000100016Q00048Q000100016Q00053Q00064Q001E00013Q00046D3Q001E00012Q00A43Q00053Q0020385Q00022Q009A012Q000200012Q002C8Q00D73Q00054Q00A43Q00064Q008C3Q000100012Q00A43Q00074Q008C3Q000100012Q00A43Q00083Q00300D3Q00030004001225012Q00054Q00D73Q00094Q00A43Q00083Q00300D3Q000600042Q00A43Q00083Q00300D3Q000700052Q00283Q000A3Q00122Q000100086Q000200018Q0002000100124Q00093Q00122Q0001000A8Q000200016Q00017Q00213Q0003103Q0053652Q73696F6E537461727454696D6503043Q007469636B030A3Q00546F74616C4D696E6564028Q0003133Q004C6173744D61696E74656E616E636554696D6503103Q004D61696E74656E616E6365436F756E74030C3Q0043752Q72656E745068617365030A3Q00536B69704672616D6573030E3Q00536B69704D696E654672616D657303113Q004C6173744F7265536B69704E6F74696679030F3Q004F7265536B69704E6F746966696564030C3Q004D617463686564526F636B7303123Q0043616D6572615368616B65526573746F72650003123Q004C6173745072696F7269747953776974636803113Q005072696F726974794C6F636B556E74696C03143Q004C6173745072696F72697479526F636B5479706503153Q005072696F7269747954797065432Q6F6C646F776E7303113Q004C6173745072696F72697479436865636B030F3Q004C617374526F636B52656672657368030D3Q0050656E64696E67537769746368010003113Q004C61737450656E64696E67537769746368030F3Q004C617374506F73436865636B506F7303103Q004C617374506F73436865636B54696D6503183Q00204D696E696E67204C2Q6F70205354415254494E473Q2E03053Q007072696E7403213Q005B466F726765204D696E696E675D205374617274696E67204D696E696E673Q2E03093Q0048656172746265617403073Q00436F2Q6E65637403043Q007461736B03053Q00737061776E031D3Q005B466F726765204D696E696E675D204D696E696E672053746172746564007F4Q00A48Q00A4000100014Q00B83Q000200020006B43Q000600013Q00046D3Q000600012Q00C43Q00014Q00A43Q00013Q0006B43Q000B00013Q00046D3Q000B00012Q002C8Q00D73Q00014Q00A43Q00023Q0012562Q0100026Q00010001000200104Q000100016Q00023Q00304Q000300046Q00023Q00122Q000100026Q00010001000200104Q000500016Q00023Q00304Q000600046Q00023Q00304Q000700046Q00023Q00304Q000800046Q00023Q00304Q000900046Q00023Q00304Q000A00046Q00026Q00015Q00104Q000B00016Q00026Q00015Q00104Q000C00016Q00023Q00304Q000D000E6Q00023Q00304Q000F00046Q00023Q00304Q001000046Q00023Q00304Q0011000E6Q00026Q00015Q00104Q001200016Q00023Q00304Q001300046Q00023Q00122Q000100026Q00010001000200104Q001400016Q00023Q00304Q001500166Q00023Q00304Q001700046Q00023Q00304Q0018000E6Q00023Q00122Q000100026Q00010001000200104Q001900016Q00033Q00122Q0001001A6Q000200018Q0002000100124Q001B3Q00122Q0001001C8Q000200016Q00048Q000100016Q00058Q000100016Q00068Q000100016Q00078Q000100016Q00093Q00206Q001D00206Q001E00066B01023Q000100022Q00A43Q000A4Q00A43Q000B4Q004C3Q000200022Q00D73Q00083Q00126A012Q001F3Q0020545Q002000066B2Q010001000100022Q00A43Q000A4Q00A43Q000C4Q009A012Q000200012Q00A43Q00093Q0020545Q001D0020385Q001E00066B01020002000100182Q00A43Q000A4Q00A43Q000D4Q00A43Q00024Q00A43Q000E4Q00A43Q000F4Q00A43Q00034Q00A43Q000B4Q00A43Q00104Q00A43Q00114Q00A43Q00124Q00A43Q00134Q00A43Q00144Q00A43Q00154Q00A43Q00164Q00A43Q00174Q00A43Q00184Q00A43Q00194Q00A43Q001A4Q00A43Q001B4Q00A43Q001C4Q00A43Q001D4Q00A43Q001E4Q00A43Q001F4Q00A43Q00204Q00163Q000200026Q00013Q00124Q001B3Q00122Q000100218Q000200016Q00013Q00033Q00073Q00030A3Q004175746F4D696E696E6703053Q007061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C696465012Q001B4Q00A47Q0020545Q0001000640012Q00050001000100046D3Q000500012Q00C43Q00014Q00A43Q00014Q00113Q00010002000640012Q000A0001000100046D3Q000A00012Q00C43Q00013Q00126A2Q0100023Q00203800023Q00032Q0030000200034Q002300013Q000300046D3Q00180001002038000600050004001225010800054Q004C0006000800020006B40006001800013Q00046D3Q001800010020540006000500060006B40006001800013Q00046D3Q0018000100300D0005000600070006772Q01000F0001000200046D3Q000F00012Q00C43Q00017Q00043Q00030A3Q004175746F4D696E696E6703043Q007461736B03043Q0077616974026Q00E03F00104Q00A47Q0020545Q00010006B43Q000F00013Q00046D3Q000F000100126A012Q00023Q00208B014Q000300122Q000100048Q000200019Q0000206Q000100066Q00013Q00046D5Q00012Q00A43Q00014Q008C3Q0001000100046D5Q00012Q00C43Q00017Q005C3Q00030A3Q004175746F4D696E696E6703043Q007469636B030D3Q004C617374536B69705265736574026Q004E40028Q0003063Q00737472696E6703063Q00666F726D6174032D3Q0020506572696F64696320636C65616E7570207C20536B692Q7065643A2564204F72654E6F7469666965643A2564030E3Q0046696E6446697273744368696C6403083Q0048756D616E6F6964030C3Q0043752Q72656E745068617365030B3Q0043752Q72656E74526F636B00030A3Q00536B69704672616D6573026Q000840032D3Q002043686172616374657220646965642F7265737061776E696E67202D20506861736520726573657420746F203003253Q0020526F636B2048503D30207C20537769746368696E6720692Q6D6564696174656C793Q2E030A3Q00546F74616C4D696E6564026Q00F03F030C3Q00536B692Q706564526F636B732Q0103073Q00556E6B6E6F776E030D3Q004C6F636B65644D696E65506F7303133Q0020492Q6D656469617465205377697463683A2003023Q002Q20030E3Q00536B69704D696E654672616D6573026Q00144003123Q004C6173745072696F7269747953776974636803143Q004C6173745072696F72697479526F636B5479706503083Q00746F6E756D62657203113Q005072696F726974794477652Q6C54696D6503113Q005072696F726974794C6F636B556E74696C03203Q00204E6F20726F636B20666F756E642061667465722048503D3020737769746368030D3Q0050656E64696E6753776974636803113Q004C61737450656E64696E67537769746368029A5Q99C93F0100030C3Q004D617463686564526F636B7303143Q005072696F72697479536B6970432Q6F6C646F776E031E3Q0020416C72656164792D6D696E696E67207377697463683A2025732Q202573026Q002440032A3Q00204E6F20726F636B20666F756E6420616674657220616C72656164792D6D696E696E672073776974636803143Q005072696F726974795363616E496E74657276616C03163Q005072696F72697479537769746368432Q6F6C646F776E03113Q004C6173745072696F72697479436865636B030F3Q005072696F72697479456E61626C6564026Q001040030F3Q004F7265536B69704E6F746966696564030E3Q00526F636B5072696F72697469657303223Q00205052494F52495459205357495443483A20257328502564292Q202573285025642903043Q006D6174682Q033Q006D6178026Q002040030E3Q004C617374526F636B536561726368030D3Q004E6F54617267657453696E636503143Q00412Q6C6F774F726546696C746572427970612Q7303153Q0049676E6F72654F726546696C74657273556E74696C026Q00184003323Q00204E6F2074617267657420666F756E642C2074656D706F726172696C792069676E6F72696E67206F72652066696C74657273030D3Q004C6173744E6F526F636B4C6F67030D3Q0053656C656374656441726561732Q033Q00412Q6C03053Q007061697273030B3Q004765744368696C6472656E2Q033Q0049734103063Q00466F6C64657203053Q004D6F64656C03413Q00204E4F20524F434B20464F554E44207C2041726561733A202573207C20537061776E733A202564207C20536B692Q7065643A202564207C2052616E67653A20256403083Q00746F737472696E67030B3Q004D696E696E6752616E6765030D3Q0020526F636B204D696E65643A20026Q002E40030D3Q00204E657720526F636B3A202573030B3Q002053776974636865643A2003013Q003F030E3Q004C6173744C2Q6F6B54617267657403083Q00506F736974696F6E030E3Q005361666548656967687449646C6503013Q0059030A3Q0047686F737453702Q6564026Q00E03F03063Q00434672616D652Q033Q006E657703013Q00582Q033Q006D696E03013Q005A03083Q00526F746174696F6E03163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F723303043Q007A65726F03173Q00412Q73656D626C79416E67756C617256656C6F63697479030D3Q00506C6174666F726D5374616E64017C033Q00A400015Q0020540001000100010006402Q0100050001000100046D3Q000500012Q00C43Q00014Q00A4000100014Q001B00010001000100122Q000100026Q0001000100024Q000200023Q00202Q0002000200034Q000100010002000E2Q000400230001000100046D3Q002300012Q00A4000100034Q00110001000100022Q00A4000200044Q0011000200010002000E54010500160001000100046D3Q00160001000EA80105001F0001000200046D3Q001F00012Q00A4000300053Q0012B7000400063Q00202Q00040004000700122Q000500086Q000600016Q000700026Q0004000700024Q000500016Q0003000500012Q00A4000300023Q00126A010400024Q00110004000100020010160103000300042Q00A4000100064Q00080001000100024Q000200076Q000300016Q00020002000200062Q0003002D0001000100046D3Q002D00010020380003000100090012250105000A4Q004C0003000500020006B40002003100013Q00046D3Q00310001000640010300410001000100046D3Q004100012Q00A4000400023Q00205400040004000B0026A7010400400001000500046D3Q004000012Q00A4000400023Q00300D0004000B00052Q00A4000400023Q00300D0004000C000D2Q00A4000400023Q00300D0004000E000F2Q00A4000400084Q008C0004000100012Q00A4000400053Q001225010500104Q009A0104000200012Q00C43Q00014Q00A4000400023Q00205400040004000C0006B4000400AB00013Q00046D3Q00AB00012Q00A4000400094Q00A4000500023Q00205400050005000C2Q00B80004000200020026A7010400AB0001000D00046D3Q00AB00010026D8000400AB0001000500046D3Q00AB00012Q00A4000500053Q00122B010600116Q000700016Q0005000700014Q000500026Q000600023Q00202Q00060006001200202Q00060006001300102Q0005001200064Q000500023Q00202Q0005000500144Q000600023Q00202Q00060006000C00202Q0005000600154Q0005000A6Q000600023Q00202Q00060006000C4Q00050002000200062Q000500620001000100046D3Q00620001001225010500164Q00A4000600023Q00203701060006000C4Q000700023Q00302Q0007000C000D4Q000700023Q00302Q0007000B00054Q000700023Q00302Q00070017000D4Q000700026Q0008000B6Q0008000100020010160107000C00082Q00A40007000C4Q003C000800064Q009A0107000200012Q00A40007000D4Q00A4000800023Q00205400080008000C2Q009A0107000200012Q00A4000700023Q00205400070007000C0006B4000700A800013Q00046D3Q00A800012Q00A40007000A4Q00A4000800023Q00205400080008000C2Q00B8000700020002000640010700800001000100046D3Q00800001001225010700164Q00A4000800053Q001274010900186Q000A00053Q00122Q000B00196Q000C00076Q00090009000C4Q000A00016Q0008000A000100122Q000800056Q0008000E6Q000800023Q00300D0008001A001B2Q00A4000800023Q00126A010900024Q00110009000100020010160108001C00092Q00A4000800023Q0010160108001D000700126A0108001E4Q00A400095Q00205400090009001F2Q00B8000800020002000640010800A00001000100046D3Q00A000012Q00A40008000F3Q0006B40008009F00013Q00046D3Q009F00012Q00A40008000F3Q00205400080008001F000640010800A00001000100046D3Q00A00001001225010800053Q000EA8010500AB0001000800046D3Q00AB00012Q00A4000900023Q001289000A00026Q000A000100024Q000A000A000800102Q00090020000A00044Q00AB00012Q00A4000700053Q001225010800214Q009A01070002000100126A010400024Q00110004000100022Q00A4000500023Q0020540005000500220006B4000500112Q013Q00046D3Q00112Q012Q00A4000500023Q0020540005000500232Q00D5000500040005000E69012400112Q01000500046D3Q00112Q012Q00A4000500023Q0010480105002300044Q000500023Q00302Q0005002200254Q000500023Q00202Q00050005000C00062Q000500112Q013Q00046D3Q00112Q012Q00A4000500023Q0020170105000500264Q000600023Q00202Q00060006000C4Q00050005000600062Q000500112Q01000100046D3Q00112Q012Q00A40005000A4Q00A4000600023Q00205400060006000C2Q00B8000500020002000640010500CC0001000100046D3Q00CC0001001225010500163Q00126A0106001E4Q00A400075Q0020540007000700272Q00B8000600020002000640010600DA0001000100046D3Q00DA00012Q00A40006000F3Q0006B4000600D900013Q00046D3Q00D900012Q00A40006000F3Q002054000600060027000640010600DA0001000100046D3Q00DA0001001225010600054Q00A4000700023Q0030920107000C000D4Q000700023Q00302Q0007000B00054Q000700023Q00302Q00070017000D4Q000700026Q0008000B6Q00080001000200102Q0007000C00084Q0007000D6Q000800023Q00202Q00080008000C4Q0007000200014Q000700023Q00202Q00070007000C00062Q0007000D2Q013Q00046D3Q000D2Q012Q00A40007000A4Q00A4000800023Q00205400080008000C2Q00B8000700020002000640010700F30001000100046D3Q00F30001001225010700163Q000EA8010500FB0001000600046D3Q00FB00010006B4000500FB00013Q00046D3Q00FB00012Q00A4000800104Q003C000900054Q003C000A00064Q007D0008000A00012Q00A4000800053Q0012B7000900063Q00202Q00090009000700122Q000A00286Q000B00056Q000C00076Q0009000C00024Q000A00016Q0008000A0001001225010800054Q00D70008000E4Q00A4000800023Q00300D0008000E000F2Q00A4000800023Q00300D0008001A00292Q00A4000800023Q0010160108001D000700046D3Q00112Q012Q00A4000700053Q0012250108002A4Q0012010900014Q007D00070009000100126A0105001E4Q00A400065Q00205400060006002B2Q00B80005000200020006400105001F2Q01000100046D3Q001F2Q012Q00A40005000F3Q0006B40005001E2Q013Q00046D3Q001E2Q012Q00A40005000F3Q00205400050005002B0006400105001F2Q01000100046D3Q001F2Q01001225010500243Q00126A0106001E4Q00A400075Q00205400070007002C2Q00B80006000200020006400106002D2Q01000100046D3Q002D2Q012Q00A40006000F3Q0006B40006002C2Q013Q00046D3Q002C2Q012Q00A40006000F3Q00205400060006002C0006400106002D2Q01000100046D3Q002D2Q01001225010600053Q00126A0107001E4Q00A400085Q00205400080008001F2Q00B80007000200020006400107003B2Q01000100046D3Q003B2Q012Q00A40007000F3Q0006B40007003A2Q013Q00046D3Q003A2Q012Q00A40007000F3Q00205400070007001F0006400107003B2Q01000100046D3Q003B2Q01001225010700054Q00A4000800023Q00205400080008002D2Q00D500080004000800064B000500020001000800046D3Q00412Q012Q001301086Q0012010800013Q0026840106004A2Q01000500046D3Q004A2Q012Q00A4000900023Q00205400090009001C2Q00D500090004000900064B000600020001000900046D3Q004A2Q012Q001301096Q0012010900014Q00A4000A00023Q002054000A000A001A002684010A00502Q01000500046D3Q00502Q012Q0013010A6Q0012010A00014Q00A4000B00023Q002054000B000B0020000640010B00562Q01000100046D3Q00562Q01001225010B00053Q00064B000B00020001000400046D3Q00592Q012Q0013010B6Q0012010B00014Q00A4000C00023Q002054000C000C000C0006B4000C00632Q013Q00046D3Q00632Q012Q00A4000C00023Q002054000C000C00262Q00A4000D00023Q002054000D000D000C2Q00A6000C000C000D2Q00A4000D00023Q002054000D000D000C0006B4000D00F12Q013Q00046D3Q00F12Q012Q00A4000D5Q002054000D000D002E0006B4000D00F12Q013Q00046D3Q00F12Q01000640010C00F12Q01000100046D3Q00F12Q010006B4000800F12Q013Q00046D3Q00F12Q010006B4000900F12Q013Q00046D3Q00F12Q010006B4000A00F12Q013Q00046D3Q00F12Q010006B4000B00F12Q013Q00046D3Q00F12Q012Q00A4000D00023Q001016010D002D00042Q00A4000D00023Q002054000D000D000B002680000D00832Q01002F00046D3Q00832Q012Q00A4000D00023Q002017010D000D00304Q000E00023Q00202Q000E000E000C4Q000D000D000E00062Q000D00832Q01000100046D3Q00832Q0100046D3Q00F12Q012Q00A4000D00114Q00A4000E00023Q002054000E000E000C2Q00B8000D000200020006B4000D00F12Q013Q00046D3Q00F12Q012Q00A4000E00023Q002054000E000E000C2Q00A4000F000A4Q003C0010000E4Q00B8000F00020002000640010F00912Q01000100046D3Q00912Q01001225010F00164Q00A400105Q0020540010001000312Q00A600100010000F000640011000972Q01000100046D3Q00972Q01001225011000054Q00A40011000A4Q003C0012000D4Q00B80011000200020006400111009D2Q01000100046D3Q009D2Q01001225011100164Q00A400125Q0020540012001200312Q00A6001200120011000640011200A32Q01000100046D3Q00A32Q01001225011200054Q00A4001300053Q0012A2011400063Q00202Q00140014000700122Q001500326Q0016000F6Q001700106Q001800116Q001900126Q0014001900024Q001500016Q00130015000100122Q0013001E6Q00145Q00202Q0014001400274Q00130002000200062Q001300BC2Q01000100046D3Q00BC2Q012Q00A40013000F3Q0006B4001300BB2Q013Q00046D3Q00BB2Q012Q00A40013000F3Q002054001300130027000640011300BC2Q01000100046D3Q00BC2Q01001225011300053Q000EA8010500C62Q01001300046D3Q00C62Q010006B4000E00C62Q013Q00046D3Q00C62Q012Q00A4001400023Q0020F500140014001400122Q001500026Q0015000100024Q0015001500134Q0014000E0015000EA8010500CE2Q01001300046D3Q00CE2Q010006B4000F00CE2Q013Q00046D3Q00CE2Q012Q00A4001400104Q003C0015000F4Q003C001600134Q007D0014001600012Q00A40014000C4Q003C0015000E4Q009A0114000200012Q00A4001400023Q0010160114000C000D2Q00A4001400023Q00300D0014000B00052Q00A4001400023Q00300D00140017000D2Q00A40014000D4Q00A4001500023Q00205400150015000C2Q009A011400020001001225011400054Q00D70014000E4Q00A4001400023Q00126A011500333Q0020540015001500342Q00A4001600023Q00205400160016001A000640011600E52Q01000100046D3Q00E52Q01001225011600053Q001225011700354Q006301150017000200102Q0014001A00154Q001400023Q00102Q0014001C00044Q001400023Q00102Q0014001D0011000E2Q000500F12Q01000700046D3Q00F12Q012Q00A4001400024Q00E90015000400070010160114002000152Q00A4000D00023Q002054000D000D000C0006B4000D00FC2Q013Q00046D3Q00FC2Q012Q00A4000D00124Q005A000E00023Q00202Q000E000E000C4Q000F00016Q000D000F000200062Q000D002D0301000100046D3Q002D03012Q0012010D00014Q00A4000E00023Q002054000E000E000C000640010E000D0201000100046D3Q000D02012Q00A4000E00023Q002054000E000E00360006B4000E000D02013Q00046D3Q000D020100126A010E00024Q008B000E000100024Q000F00023Q00202Q000F000F00364Q000E000E000F00262Q000E000D0201002400046D3Q000D02012Q0012010D5Q0006B4000D002D03013Q00046D3Q002D03012Q00A4000E00023Q0012F9000F00026Q000F0001000200102Q000E0036000F4Q000E00023Q00202Q000E000E000C4Q000F00026Q0010000B6Q00100001000200102Q000F000C00104Q000F000D6Q001000023Q00202Q00100010000C4Q000F000200014Q000F00023Q00202Q000F000F000C00062Q000F002402013Q00046D3Q002402012Q00A4000F00023Q00300D000F0037000D00046D3Q004E02012Q00A4000F00023Q002054000F000F0037000640010F002D0201000100046D3Q002D02012Q00A4000F00023Q00126A011000024Q0011001000010002001016010F0037001000046D3Q004E020100126A010F00024Q005B010F000100024Q001000023Q00202Q0010001000374Q000F000F0010000E2Q000F004E0201000F00046D3Q004E02012Q00A4000F5Q002054000F000F00380006B4000F004C02013Q00046D3Q004C02012Q00A4000F00023Q002054000F000F00390006B4000F004202013Q00046D3Q0042020100126A010F00024Q0011000F000100022Q00A4001000023Q0020540010001000390006B30010004E0201000F00046D3Q004E02012Q00A4000F00023Q00126A011000024Q001100100001000200203400100010003A001016010F003900102Q00A4000F00053Q0012250110003B4Q0012011100014Q007D000F0011000100046D3Q004E02012Q00A4000F00023Q00300D000F003900052Q00A4000F00023Q002054000F000F000C000640010F00B30201000100046D3Q00B302012Q00A4000F00023Q002054000F000F003C0006B4000F005D02013Q00046D3Q005D020100126A010F00024Q005B010F000100024Q001000023Q00202Q00100010003C4Q000F000F0010000E2Q001B00B30201000F00046D3Q00B302012Q00A4000F00134Q0002000F0001000200122Q001000053Q00122Q001100056Q00125Q00202Q00120012003D4Q001200123Q000E2Q0005006B0201001200046D3Q006B02012Q00A400125Q00205400120012003D2Q002E011200123Q0006400112006C0201000100046D3Q006C02010012250112003E3Q00126A0113003F4Q00A4001400023Q0020540014001400142Q006400130002001500046D3Q00720201002034001100110013000677011300710201000100046D3Q007102010006B4000F00A102013Q00046D3Q00A102012Q00A400135Q00205400130013003D2Q002E011300133Q002680001300910201000500046D3Q0091020100126A0113003F3Q0020380014000F00402Q0030001400154Q002300133Q001500046D3Q008E0201002038001800170041001225011A00424Q004C0018001A00020006400118008A0201000100046D3Q008A0201002038001800170041001225011A00434Q004C0018001A00020006B40018008E02013Q00046D3Q008E02010020380018001700402Q00B80018000200022Q002E011800184Q00E9001000100018000677011300800201000200046D3Q0080020100046D3Q00A1020100126A0113003F4Q00A400145Q00205400140014003D2Q006400130002001500046D3Q009F02010020380018000F00092Q003C001A00174Q004C0018001A00020006B40018009F02013Q00046D3Q009F02010020380019001800402Q00B80019000200022Q002E011900194Q00E9001000100019000677011300960201000200046D3Q009602012Q00A4001300053Q00129C001400063Q00202Q00140014000700122Q001500443Q00122Q001600456Q001700126Q0016000200024Q001700106Q001800116Q00195Q00202Q0019001900462Q004C0014001900022Q0044011500016Q0013001500014Q001300023Q00122Q001400026Q00140001000200102Q0013003C00140006B4000E00D402013Q00046D3Q00D402012Q00A4000F00023Q002054000F000F000C000640010F00D40201000100046D3Q00D402012Q00A4000F00053Q00125C001000476Q0011000A6Q0012000E6Q00110002000200062Q001100C10201000100046D3Q00C10201001225011100164Q007A0010001000112Q0047000F000200014Q000F00146Q001000106Q000F000200014Q000F00026Q001000023Q00202Q00100010001200202Q00100010001300102Q000F001200104Q000F00023Q00300D000F000B00052Q00A4000F00023Q00300D000F000E000F2Q00A4000F00023Q00300D000F001A00482Q00A4000F00023Q00300D000F0017000D00046D3Q002D0301000640010E00F70201000100046D3Q00F702012Q00A4000F00023Q002054000F000F000C0006B4000F00F702013Q00046D3Q00F702012Q00A4000F00053Q001264011000063Q00202Q00100010000700122Q001100496Q0012000A6Q001300023Q00202Q00130013000C4Q00120002000200062Q001200E50201000100046D3Q00E50201001225011200164Q0095011000124Q009A000F3Q00014Q000F00146Q0010000A6Q001100023Q00202Q00110011000C4Q001000116Q000F3Q000100122Q000F00056Q000F000E6Q000F00023Q00302Q000F000B00054Q000F00023Q00302Q000F000E000F4Q000F00023Q00302Q000F001A00486Q00013Q00044Q002D03010006B4000E002D03013Q00046D3Q002D03012Q00A4000F00023Q002054000F000F000C0006B4000F002D03013Q00046D3Q002D03012Q00A4000F00023Q002054000F000F000C000659000E002D0301000F00046D3Q002D03012Q00A4000F00053Q00125C0010004A6Q0011000A6Q0012000E6Q00110002000200062Q001100090301000100046D3Q000903010012250111004B3Q001225011200194Q00D90013000A6Q001400023Q00202Q00140014000C4Q00130002000200062Q001300110301000100046D3Q001103010012250113004B4Q007A0010001000132Q007B000F000200014Q000F00146Q0010000A6Q001100023Q00202Q00110011000C4Q001000116Q000F3Q000100122Q000F00056Q000F000E6Q000F00023Q00300D000F000B00052Q009E000F00023Q00302Q000F000E000F4Q000F00023Q00302Q000F001A00484Q000F00023Q00302Q000F0017000D4Q000F00156Q001000023Q00202Q00100010000C4Q000F000200020006B4000F002C03013Q00046D3Q002C03012Q00A4001000023Q0020540011000F004D0010160110004C00112Q00C43Q00014Q00A4000D00164Q007E000E00046Q000D000200014Q000D00023Q00202Q000D000D000C00062Q000D005C0301000100046D3Q005C03012Q00A4000D5Q0020DF000D000D004E00202Q000E0002004D00202Q000F000E004F00202Q0010000D001B00062Q000F004F0301001000046D3Q004F03012Q00A4000F5Q002019010F000F00504Q000F000F3Q00202Q000F000F005100202Q0010000E004F4Q00100010000F00122Q001100523Q00202Q00110011005300202Q0012000E005400122Q001300333Q00202Q0013001300554Q001400106Q0015000D6Q00130015000200202Q0014000E00564Q00110014000200202Q00120002005200202Q0012001200574Q00110011001200102Q00020052001100126A010F00593Q002031010F000F005A00102Q00020058000F00122Q000F00593Q00202Q000F000F005A00102Q0002005B000F00202Q000F0003005C00062Q000F00590301000100046D3Q0059030100300D0003005C00152Q00A4000F00023Q00300D000F000B00052Q00C43Q00014Q00A4000D00023Q002054000D000D000E000EA80105006C0301000D00046D3Q006C03012Q00A4000D00024Q0018000E00023Q00202Q000E000E000E00202Q000E000E001300102Q000D000E000E00122Q000D00593Q00202Q000D000D005A00102Q00020058000D00122Q000D00593Q00202Q000D000D005A00102Q0002005B000D6Q00014Q00A4000D00154Q00A4000E00023Q002054000E000E000C2Q00B8000D00020002000640010D00750301000100046D3Q007503012Q00A4000E00023Q00300D000E000C000D2Q00C43Q00014Q00A4000E00174Q003C000F00024Q003C001000034Q003C0011000D4Q003C00126Q007D000E001200012Q00C43Q00017Q00103Q0003023Q005F4703053Q00466F726765030A3Q004661726D436F6E66696703083Q004175746F4661726D03083Q0053746F704661726D0100030E3Q004661726D5549456C656D656E7473030E3Q004175746F4661726D546F2Q676C6503053Q007063612Q6C03053Q005469746C65030B3Q004175746F204D696E696E6703073Q00436F6E74656E7403253Q004175746F204661726D2064697361626C656420746F2061766F696420636F6E666C6963747303083Q004475726174696F6E027Q0040030A3Q004175746F4D696E696E6701343Q0006B43Q002600013Q00046D3Q0026000100126A2Q0100013Q0020540001000100020006FE000200070001000100046D3Q000700010020540002000100030006B40002002600013Q00046D3Q002600010020540003000200040006B40003002600013Q00046D3Q002600010020540003000100050006B40003001200013Q00046D3Q001200010020540003000100052Q008C00030001000100046D3Q0020000100300D0002000400060006FE000300160001000100046D3Q001600010020540003000100070006B40003001F00013Q00046D3Q001F00010020540004000300080006B40004001F00013Q00046D3Q001F000100126A010400093Q00066B01053Q000100012Q003C3Q00034Q009A0104000200012Q001D00036Q00A400036Q005200043Q000300302Q0004000A000B00302Q0004000C000D00302Q0004000E000F4Q0003000200012Q00A4000100013Q0010162Q0100103Q0006B43Q002F00013Q00046D3Q002F00012Q00A4000100024Q008C0001000100012Q00A4000100034Q008C00010001000100046D3Q003300012Q00A4000100044Q008C0001000100012Q00A4000100054Q008C0001000100012Q00C43Q00013Q00013Q00023Q00030E3Q004175746F4661726D546F2Q676C652Q033Q0053657400064Q00DE7Q00206Q000100206Q00024Q00029Q00000200016Q00019Q002Q0001044Q00A400016Q003C00026Q009A2Q01000200012Q00C43Q00017Q00023Q00030E3Q00537475636B446574656374696F6E03073Q00456E61626C656401044Q00A400015Q0020540001000100010010162Q0100024Q00C43Q00017Q00023Q00030E3Q00537475636B446574656374696F6E03153Q00506F736974696F6E436865636B496E74657276616C01044Q00A400015Q0020540001000100010010162Q0100024Q00C43Q00017Q00023Q00030E3Q00537475636B446574656374696F6E03113Q00506F736974696F6E5468726573686F6C6401044Q00A400015Q0020540001000100010010162Q0100024Q00C43Q00017Q00073Q0003053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403163Q004D61696E74656E616E636520706572666F726D65642103083Q004475726174696F6E027Q0040000B3Q00126A012Q00013Q00066B2Q013Q000100012Q00A48Q009A012Q000200012Q00A43Q00014Q005200013Q000300302Q00010002000300302Q00010004000500302Q0001000600076Q000200012Q00C43Q00013Q00018Q00034Q00A48Q008C3Q000100012Q00C43Q00017Q00103Q0003103Q0053652Q73696F6E537461727454696D65028Q0003043Q007469636B03083Q002Q303A2Q303A2Q3003063Q006763696E666F026Q004E40030A3Q00546F74616C4D696E656403053Q005469746C65030C3Q004D696E696E6720537461747303073Q00436F6E74656E7403063Q00737472696E6703063Q00666F726D6174033E3Q00557074696D653A2025730A4D696E65643A2025640A4D504D3A20252E31660A4D61696E74656E616E63653A2025640A4D656D6F72793A20252E3166204B4203103Q004D61696E74656E616E6365436F756E7403083Q004475726174696F6E026Q00144000374Q00A47Q0020545Q0001000EA80102000D00013Q00046D3Q000D00012Q00A43Q00013Q0012EA000100036Q0001000100024Q00025Q00202Q0002000200014Q0001000100026Q0002000200064Q000E0001000100046D3Q000E0001001225012Q00043Q00126A2Q0100054Q00110001000100022Q00A400025Q002054000200020001000EA80102001C0001000200046D3Q001C000100126A010200034Q00AD0002000100024Q00035Q00202Q0003000300014Q00020002000300202Q00020002000600062Q0002001D0001000100046D3Q001D0001001225010200023Q000EA8010200240001000200046D3Q002400012Q00A400035Q0020540003000300072Q00A9000300030002000640010300250001000100046D3Q00250001001225010300024Q00A4000400024Q007201053Q000300302Q00050008000900122Q0006000B3Q00202Q00060006000C00122Q0007000D6Q00088Q00095Q00202Q0009000900074Q000A00036Q000B5Q00202Q000B000B000E4Q000C00016Q0006000C000200102Q0005000A000600302Q0005000F00104Q0004000200016Q00017Q00073Q00030D3Q0053656C65637465644172656173028Q0003053Q0070616972732Q0103053Q007461626C6503063Q00696E7365727403043Q00736F727401364Q00A400015Q0006B40001000500013Q00046D3Q000500012Q004600016Q00D7000100014Q00A4000100023Q0020540001000100012Q002E2Q0100013Q002680000100110001000200046D3Q001100012Q00A4000100033Q0006390102000E00013Q00046D3Q000E00012Q00A400026Q00B80001000200022Q00D7000100013Q00046D3Q003300012Q004600015Q00120D010200036Q000300023Q00202Q0003000300014Q00020002000400044Q0020000100126A010700034Q009F010800046Q000900066Q000800096Q00073Q000900044Q001E00010020090001000B00040006770107001D0001000200046D3Q001D0001000677010200170001000200046D3Q001700012Q004600026Q0047010200013Q00122Q000200036Q000300016Q00020002000400044Q002D000100126A010600053Q0020540006000600062Q00A4000700014Q003C000800054Q007D000600080001000677010200280001000100046D3Q0028000100126A010200053Q0020540002000200072Q00A4000300014Q009A0102000200012Q00122Q016Q00D700016Q00C43Q00017Q000C3Q00030E3Q0046696C746572536C6F74314F7265030E3Q0046696C746572536C6F74324F7265030E3Q0046696C746572536C6F74334F726503063Q00286E6F6E652903063Q0069706169727303053Q007461626C6503063Q00696E73657274030D3Q0043752Q72656E744F7074696F6E03043Q007479706503053Q007063612Q6C03133Q002853656C656374206172656120666972737429028Q00015D4Q00A4000100014Q003C00026Q00B80001000200022Q00D700016Q0046000100034Q00A4000200023Q0020540002000200012Q00A4000300023Q0020540003000300022Q00A4000400023Q0020540004000400032Q00CD0001000300012Q0046000200013Q001225010300044Q00CD00020001000100126A010300054Q00A400046Q006400030002000500046D3Q0018000100126A010800063Q0020540008000800072Q003C000900024Q003C000A00074Q007D0008000A0001000677010300130001000200046D3Q001300010002BC00035Q00126A010400054Q003C000500014Q006400040002000600046D3Q005A00010006B40008005900013Q00046D3Q0059000100205400090008000800126A010A00094Q003C000B00094Q00B8000A00020002002680000A00290001000600046D3Q00290001000639010A00310001000900046D3Q003100010006B40009003000013Q00046D3Q003000012Q0046000A00014Q003C000B00094Q00CD000A00010001000640010A00310001000100046D3Q003100012Q0046000A5Q00126A010B000A3Q00066B010C0001000100022Q003C3Q00084Q003C3Q00024Q009A010B000200012Q0046000B5Q00126A010C00054Q003C000D000A4Q0064000C0002000E00046D3Q004A00010006B40010004A00013Q00046D3Q004A00010026A70110004A0001000B00046D3Q004A00012Q003C001100034Q003C001200024Q003C001300104Q004C0011001300020006B40011004A00013Q00046D3Q004A000100126A011100063Q0020540011001100072Q003C0012000B4Q003C001300104Q007D001100130001000677010C003B0001000200046D3Q003B00012Q002E010C000B3Q002680000C00530001000C00046D3Q005300012Q0046000C00013Q001225010D00044Q00CD000C000100012Q003C000B000C3Q00126A010C000A3Q00066B010D0002000100022Q003C3Q00084Q003C3Q000B4Q009A010C000200012Q001D00096Q001D00075Q0006770104001F0001000200046D3Q001F00012Q00C43Q00013Q00033Q00013Q0003063Q00697061697273020D3Q00126A010200014Q003C00036Q006400020002000400046D3Q00080001000668000600080001000100046D3Q000800012Q0012010700014Q003A000700023Q000677010200040001000200046D3Q000400012Q001201026Q003A000200024Q00C43Q00017Q00013Q0003073Q005265667265736800054Q00C77Q00206Q00014Q000200018Q000200016Q00017Q00013Q002Q033Q0053657400054Q00C77Q00206Q00014Q000200018Q000200016Q00017Q00153Q00030B3Q0043752Q72656E74526F636B0003053Q007461626C6503043Q0066696E64030B3Q005B412Q6C2041726561735D030D3Q0053656C65637465644172656173028Q0003093Q00417265614C6162656C03093Q00412Q6C20417265617303063Q00636F6E63617403023Q002C2003053Q007063612Q6C030D3Q0053656C6563746564526F636B73030E3Q00526F636B5072696F726974696573030C3Q00526F636B44726F70646F776E03043Q007461736B03053Q00737061776E03063Q00737472696E6703063Q00666F726D6174031F3Q0041726561733A202573207C20526F636B7320617661696C61626C653A2025642Q033Q00412Q6C015E4Q00602Q015Q00302Q00010001000200122Q000100033Q00202Q0001000100044Q00025Q00122Q000300056Q00010003000200062Q0001001000013Q00046D3Q001000012Q00A4000200014Q001001035Q00102Q0002000600034Q000200026Q000300016Q00020002000100044Q001F00012Q002E01025Q0026800002001A0001000700046D3Q001A00012Q00A4000200014Q001001035Q00102Q0002000600034Q000200026Q000300016Q00020002000100044Q001F00012Q00A4000200013Q001016010200064Q00A4000200024Q0012010300014Q009A0102000200012Q00A4000200033Q0020540002000200080006B40002003900013Q00046D3Q003900010006B40001002800013Q00046D3Q00280001001225010200093Q000640010200330001000100046D3Q003300012Q002E01025Q000EA8010700320001000200046D3Q0032000100126A010200033Q00205101020002000A4Q00035Q00122Q0004000B6Q00020004000200062Q000200330001000100046D3Q00330001001225010200093Q00126A0103000C3Q00066B01043Q000100022Q00A43Q00034Q003C3Q00024Q009A0103000200012Q001D00026Q00A4000200014Q004600035Q0010160102000D00032Q00C2000200016Q00035Q00102Q0002000E00034Q000200033Q00202Q00020002000F00062Q0002004900013Q00046D3Q0049000100126A010200103Q00205400020002001100066B01030001000100022Q00A43Q00034Q00A43Q00044Q009A0102000200012Q00A4000200053Q00126A010300123Q002054000300030013001225010400143Q0006B40001005200013Q00046D3Q00520001001225010500153Q000640010500590001000100046D3Q005900012Q002E01055Q000EA8010700580001000500046D3Q005800012Q002E01055Q000640010500590001000100046D3Q00590001001225010500154Q00A4000600044Q002E010600064Q0095010300064Q005301023Q00012Q00C43Q00013Q00023Q00033Q0003093Q00417265614C6162656C2Q033Q0053657403013Q002000084Q009F7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q00063Q0003053Q007063612Q6C03043Q007461736B03043Q0077616974029A5Q99B93F03093Q00526F636B4C6162656C030D3Q005072696F726974794C6162656C001E3Q00126A012Q00013Q00066B2Q013Q000100012Q00A48Q00633Q0002000100124Q00023Q00206Q000300122Q000100048Q0002000100124Q00013Q00066B2Q010001000100022Q00A48Q00A43Q00014Q009A012Q000200012Q00A47Q0020545Q00050006B43Q001500013Q00046D3Q0015000100126A012Q00013Q00066B2Q010002000100012Q00A48Q009A012Q000200012Q00A47Q0020545Q00060006B43Q001D00013Q00046D3Q001D000100126A012Q00013Q00066B2Q010003000100012Q00A48Q009A012Q000200012Q00C43Q00013Q00043Q00023Q00030C3Q00526F636B44726F70646F776E2Q033Q0053657400064Q00267Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00043Q00030C3Q00526F636B44726F70646F776E03073Q0052656672657368028Q0003123Q00284E6F20726F636B7320696E206172656129000F4Q006A7Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200046D3Q000A00012Q00A4000200013Q0006400102000D0001000100046D3Q000D00012Q0046000200013Q001225010300044Q00CD0002000100012Q007D3Q000200012Q00C43Q00017Q00033Q0003093Q00526F636B4C6162656C2Q033Q0053657403103Q0020286E6F6E652073656C65637465642900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403203Q002053656C65637420322B20726F636B7320746F20736574207072696F7269747900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q000B3Q0003053Q004172656173026Q00F03F030C3Q004172656144726F70646F776E03053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403063Q00466F756E642003073Q002061726561732103083Q004475726174696F6E027Q004000204Q0070016Q00122Q000100013Q00122Q000200028Q0002000200064Q000700013Q00046D3Q000700012Q00C43Q00014Q00A43Q00024Q0032000100018Q000200026Q00018Q00033Q00206Q000300064Q001400013Q00046D3Q0014000100126A012Q00043Q00066B2Q013Q000100022Q00A43Q00034Q00A43Q00014Q009A012Q000200012Q00A43Q00044Q00C900013Q000300302Q00010005000600122Q000200086Q000300016Q000300033Q00122Q000400096Q00020002000400102Q00010007000200302Q0001000A000B6Q000200016Q00013Q00013Q00023Q00030C3Q004172656144726F70646F776E03073Q005265667265736800064Q0094016Q00206Q000100206Q00024Q000200018Q000200016Q00017Q001E3Q00030D3Q0053656C65637465644172656173030C3Q004172656144726F70646F776E03053Q007063612Q6C030D3Q0053656C6563746564526F636B73030E3Q00526F636B5072696F726974696573030C3Q00526F636B44726F70646F776E030C3Q0053656C65637465644F726573030E3Q00526F636B4F726546696C7465727303043Q00526F636B0003043Q004F726573030B3Q004F726544726F70646F776E026Q00F03F026Q000840030A3Q0046696C746572536C6F742Q033Q004F726503103Q004C61737446696C746572536F75726365030E3Q004C61737446696C746572526F636B030B3Q0043752Q72656E74526F636B03093Q00417265614C6162656C03093Q00526F636B4C6162656C03083Q004F72654C6162656C030D3Q005072696F726974794C6162656C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403173Q00412Q6C2073656C656374696F6E7320636C65617265642103083Q004475726174696F6E027Q004003383Q0020412Q6C2073656C656374696F6E7320636C6561726564202841726561732C20526F636B732C204F7265732C205072696F72697469657329009D4Q00C29Q0000015Q00104Q000100016Q00013Q00206Q000200064Q000B00013Q00046D3Q000B000100126A012Q00033Q00066B2Q013Q000100012Q00A43Q00014Q009A012Q000200012Q00A48Q004600015Q001016012Q000400012Q00C29Q0000015Q00104Q000500016Q00013Q00206Q000600064Q001900013Q00046D3Q0019000100126A012Q00033Q00066B2Q010001000100012Q00A43Q00014Q009A012Q000200012Q00A48Q000100015Q00104Q000700019Q004Q000100036Q00023Q000200302Q00020009000A4Q00035Q00102Q0002000B00034Q00033Q000200302Q00030009000A4Q00045Q00102Q0003000B00044Q00043Q000200302Q00040009000A4Q00055Q00102Q0004000B00054Q000100030001001016012Q000800012Q00A43Q00013Q0020545Q000C0006B43Q003400013Q00046D3Q0034000100126A012Q00033Q00066B2Q010002000100012Q00A43Q00014Q009A012Q00020001001225012Q000D3Q0012252Q01000E3Q0012250102000D3Q0004B13Q005200012Q00A4000400013Q0012250105000F4Q003C000600033Q001225010700094Q007A0005000500072Q00A60004000400052Q00A4000500013Q00129B0106000F6Q000700033Q00122Q000800106Q0006000600084Q00050005000600062Q0004004A00013Q00046D3Q004A000100126A010600033Q00066B01070003000100012Q003C3Q00044Q009A0106000200010006B40005005000013Q00046D3Q0050000100126A010600033Q00066B01070004000100012Q003C3Q00054Q009A0106000200012Q001D00045Q00041C012Q003800012Q00A43Q00023Q00300D3Q0011000A2Q00A43Q00023Q00300D3Q0012000A2Q00A43Q00034Q0077000100018Q000200016Q00013Q00206Q000600064Q006200013Q00046D3Q0062000100126A012Q00033Q00066B2Q010005000100022Q00A43Q00014Q00A43Q00044Q009A012Q000200012Q00A43Q00054Q0077000100018Q000200016Q00013Q00206Q000C00064Q006E00013Q00046D3Q006E000100126A012Q00033Q00066B2Q010006000100022Q00A43Q00014Q00A43Q00064Q009A012Q000200012Q00A43Q00023Q00300D3Q0013000A2Q00A43Q00013Q0020545Q00140006B43Q007800013Q00046D3Q0078000100126A012Q00033Q00066B2Q010007000100012Q00A43Q00014Q009A012Q000200012Q00A43Q00013Q0020545Q00150006B43Q008000013Q00046D3Q0080000100126A012Q00033Q00066B2Q010008000100012Q00A43Q00014Q009A012Q000200012Q00A43Q00013Q0020545Q00160006B43Q008800013Q00046D3Q0088000100126A012Q00033Q00066B2Q010009000100012Q00A43Q00014Q009A012Q000200012Q00A43Q00013Q0020545Q00170006B43Q009000013Q00046D3Q0090000100126A012Q00033Q00066B2Q01000A000100012Q00A43Q00014Q009A012Q000200012Q00A43Q00074Q003C012Q000100016Q00086Q00013Q000300302Q00010018001900302Q0001001A001B00302Q0001001C001D6Q000200016Q00093Q00122Q0001001E6Q000200018Q000200016Q00013Q000B3Q00023Q00030C3Q004172656144726F70646F776E2Q033Q0053657400064Q00267Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030C3Q00526F636B44726F70646F776E2Q033Q0053657400064Q00267Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030B3Q004F726544726F70646F776E2Q033Q0053657400064Q00267Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q001E016Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q007D3Q000200012Q00C43Q00017Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q001E016Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q007D3Q000200012Q00C43Q00017Q00023Q00030C3Q00526F636B44726F70646F776E03073Q005265667265736800064Q0094016Q00206Q000100206Q00024Q000200018Q000200016Q00017Q00043Q00030B3Q004F726544726F70646F776E03073Q0052656672657368028Q00030F3Q00284E6F206F72657320666F756E6429000F4Q006A7Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200046D3Q000A00012Q00A4000200013Q0006400102000D0001000100046D3Q000D00012Q0046000200013Q001225010300044Q00CD0002000100012Q007D3Q000200012Q00C43Q00017Q00033Q0003093Q00417265614C6162656C2Q033Q00536574030A3Q0020412Q6C20417265617300064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003093Q00526F636B4C6162656C2Q033Q0053657403103Q0020286E6F6E652073656C65637465642900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403273Q00476C6F62616C204F726573202866612Q6C6261636B293A20286E6F6E652073656C65637465642900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403203Q002053656C65637420322B20726F636B7320746F20736574207072696F7269747900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00023Q0003053Q00526F636B73026Q00F03F000B4Q0070016Q00122Q000100013Q00122Q000200028Q0002000200064Q000700013Q00046D3Q000700012Q00C43Q00014Q00A43Q00014Q00122Q016Q009A012Q000200012Q00C43Q00017Q00103Q0003043Q004F726573026Q00F03F03063Q006970616972732Q01030C3Q0053656C65637465644F72657303053Q007461626C6503063Q00696E7365727403193Q004175746F5472696D496E76616C696453656C656374696F6E73030B3Q004F726544726F70646F776E03053Q007063612Q6C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403103Q004F726573207265667265736865643A2003083Q004475726174696F6E027Q004000434Q0070016Q00122Q000100013Q00122Q000200028Q0002000200064Q000700013Q00046D3Q000700012Q00C43Q00014Q00A43Q00014Q00122Q0100014Q009A012Q000200012Q00467Q00126A2Q0100034Q00A4000200024Q006400010002000300046D3Q001000010020093Q000500040006772Q01000F0001000200046D3Q000F00012Q004600015Q00120D010200036Q000300033Q00202Q0003000300054Q00020002000400044Q002000012Q00A600073Q00060006B40007002000013Q00046D3Q0020000100126A010700063Q0020540007000700072Q003C000800014Q003C000900064Q007D000700090001000677010200180001000200046D3Q001800012Q00A4000200033Q0020540002000200080006B40002002E00013Q00046D3Q002E00012Q002E010200014Q00A4000300033Q0020540003000300052Q002E010300033Q0006590002002E0001000300046D3Q002E00012Q00A4000200033Q0010160102000500012Q00A4000200043Q0020540002000200090006B40002003800013Q00046D3Q0038000100126A0102000A3Q00066B01033Q000100032Q00A43Q00044Q00A43Q00024Q00A43Q00034Q009A0102000200012Q00A4000200054Q006101033Q000300302Q0003000B000C00122Q0004000E6Q000500026Q000500056Q00040004000500102Q0003000D000400302Q0003000F00104Q0002000200012Q00C43Q00013Q00013Q00063Q00030B3Q004F726544726F70646F776E03073Q0052656672657368028Q00030F3Q00284E6F206F72657320666F756E6429030C3Q0053656C65637465644F7265732Q033Q00536574001A4Q006A7Q00206Q000100206Q00024Q000200016Q000200023Q000E2Q0003000A0001000200046D3Q000A00012Q00A4000200013Q0006400102000D0001000100046D3Q000D00012Q0046000200013Q001225010300044Q00CD0002000100012Q007D3Q000200012Q00A43Q00023Q0020545Q00052Q002E016Q000EA80103001900013Q00046D3Q001900012Q00A47Q0020E75Q000100206Q00064Q000200023Q00202Q0002000200056Q000200012Q00C43Q00017Q00113Q00030D3Q0053656C65637465644172656173028Q002Q033Q00412Q6C03053Q007461626C6503063Q00636F6E63617403023Q002C2003043Q004E6F6E6503093Q00412Q6C20417265617303053Q005469746C6503083Q002041726561733A2003083Q00746F737472696E6703073Q00436F6E74656E7403063Q00737472696E6703063Q00666F726D6174031E3Q002053656C65637465643A2025732Q0A20526F636B7320282564293A0A257303083Q004475726174696F6E026Q00244000434Q00A47Q0020545Q00012Q002E016Q000EA80102000A00013Q00046D3Q000A00012Q00A47Q0020545Q00012Q002E016Q000640012Q000B0001000100046D3Q000B0001001225012Q00034Q00A400015Q0020540001000100012Q002E2Q0100013Q002680000100140001000200046D3Q001400012Q00A4000100014Q00110001000100020006402Q0100150001000100046D3Q001500012Q00A4000100024Q00A4000200034Q00110002000100022Q002E010300013Q000EA8010200210001000300046D3Q0021000100126A010300043Q0020510103000300054Q000400013Q00122Q000500066Q00030005000200062Q000300220001000100046D3Q00220001001225010300074Q00A400045Q0020540004000400012Q002E010400043Q000EA80102002F0001000400046D3Q002F000100126A010400043Q0020270004000400054Q00055Q00202Q00050005000100122Q000600066Q00040006000200062Q000400300001000100046D3Q00300001001225010400084Q00A4000500044Q001D01063Q000300122Q0007000A3Q00122Q0008000B6Q00098Q0008000200024Q00070007000800102Q00060009000700122Q0007000D3Q00202Q00070007000E00122Q0008000F4Q003C000900044Q002E010A00014Q003C000B00034Q004C0007000B00020010160106000C000700300D0006001000112Q009A0105000200012Q00C43Q00017Q00023Q00030A3Q00466C696768744D6F6465026Q00F03F01044Q00A400015Q00205400023Q00020010162Q01000100022Q00C43Q00017Q00063Q00030A3Q0043616D6572614D6F646503043Q007479706503053Q007461626C65026Q00F03F030A3Q004175746F4D696E696E6703193Q002043616D657261204D6F6465206368616E67656420746F3A20011A4Q00A400015Q00126A010200024Q003C00036Q00B8000200020002002680000200090001000300046D3Q0009000100205400023Q00040006400102000A0001000100046D3Q000A00012Q003C00025Q0010162Q01000100022Q00A400015Q0020540001000100050006B40001001300013Q00046D3Q001300012Q00A4000100014Q008C0001000100012Q00A4000100024Q008C0001000100012Q00A4000100033Q0012CF000200066Q00035Q00202Q0003000300014Q0002000200034Q0001000200016Q00017Q00013Q0003093Q004D696E6544656C617901034Q00A400015Q0010162Q0100014Q00C43Q00017Q00013Q00030F3Q004D696E6544656C61794A692Q74657201034Q00A400015Q0010162Q0100014Q00C43Q00017Q00013Q0003103Q00486F72697A6F6E74616C4F2Q6673657401034Q00A400015Q0010162Q0100014Q00C43Q00017Q00013Q0003163Q00526F746174696F6E446561645A6F6E6554726176656C01034Q00A400015Q0010162Q0100014Q00C43Q00017Q001C3Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7303063Q006970616972732Q0103053Q007461626C6503063Q00696E73657274030D3Q0053656C6563746564526F636B73030B3Q0043752Q72656E74526F636B00030E3Q00526F636B5072696F726974696573026Q00F03F03093Q00526F636B4C6162656C028Q0003063Q00636F6E63617403023Q002C20030F3Q00286E6F6E652073656C65637465642903053Q007063612Q6C030E3Q00526F636B436F756E744C6162656C030D3Q005072696F726974794C6162656C2Q033Q003173742Q033Q00326E642Q033Q003372642Q033Q003474682Q033Q003574682Q033Q003674682Q033Q003774682Q033Q0038746803023Q00746803023Q003A2001834Q003C00016Q00A400025Q0020540002000200010006B40002001D00013Q00046D3Q001D00012Q004600025Q00126A010300024Q00A4000400014Q006400030002000500046D3Q000B00010020090002000700030006770103000A0001000200046D3Q000A00012Q004600035Q00126A010400024Q003C00056Q006400040002000600046D3Q001A00012Q00A60009000200080006B40009001A00013Q00046D3Q001A000100126A010900043Q0020540009000900052Q003C000A00034Q003C000B00084Q007D0009000B0001000677010400120001000200046D3Q001200012Q003C000100034Q00A400025Q0010160102000600012Q00A4000200023Q00300D0002000700082Q00A400026Q004600035Q0010160102000900032Q00A400025Q0020540002000200062Q002E010200023Q00120D010300026Q00045Q00202Q0004000400064Q00030002000500044Q003100012Q00A400085Q0020540008000800092Q00D500090002000600203400090009000A2Q003F0008000700090006770103002C0001000200046D3Q002C00012Q00A4000300033Q00205400030003000B0006B40003004800013Q00046D3Q00480001000EA8010C00410001000200046D3Q0041000100126A010300043Q00202700030003000D4Q00045Q00202Q00040004000600122Q0005000E6Q00030005000200062Q000300420001000100046D3Q004200010012250103000F3Q00126A010400103Q00066B01053Q000100022Q00A43Q00034Q003C3Q00034Q009A0104000200012Q001D00036Q00A4000300033Q0020540003000300110006B40003005200013Q00046D3Q0052000100126A010300103Q00066B01040001000100032Q00A43Q00034Q00A43Q00044Q003C3Q00014Q009A0103000200012Q00A4000300033Q0020540003000300120006B40003008200013Q00046D3Q00820001000EA8010A007E0001000200046D3Q007E00012Q0046000300083Q001225010400133Q001225010500143Q001225010600153Q0012AF000700163Q00122Q000800173Q00122Q000900183Q00122Q000A00193Q00122Q000B001A6Q0003000800012Q004600045Q00120D010500026Q00065Q00202Q0006000600064Q00050002000700044Q0075000100126A010A00043Q002054000A000A00052Q003C000B00044Q00A6000C00030008000640010C00710001000100046D3Q007100012Q003C000C00083Q001225010D001B4Q007A000C000C000D001225010D001C4Q003C000E00094Q007A000C000C000E2Q007D000A000C0001000677010500680001000200046D3Q0068000100126A010500103Q00066B01060002000100022Q00A43Q00034Q003C3Q00044Q009A0105000200012Q001D00035Q00046D3Q0082000100126A010300103Q00066B01040003000100012Q00A43Q00034Q009A0103000200012Q00C43Q00013Q00043Q00033Q0003093Q00526F636B4C6162656C2Q033Q0053657403013Q002000084Q009F7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q00023Q00030E3Q00526F636B436F756E744C6162656C2Q033Q0053657400084Q000C7Q00206Q000100206Q00024Q000200016Q000300026Q000200039Q0000016Q00017Q00063Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403013Q002003053Q007461626C6503063Q00636F6E63617403023Q002Q20000C4Q00D07Q00206Q000100206Q000200122Q000200033Q00122Q000300043Q00202Q0003000300054Q000400013Q00122Q000500066Q0003000500024Q0002000200036Q000200016Q00017Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403203Q002053656C65637420322B20726F636B7320746F20736574207072696F7269747900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00013Q00030F3Q005072696F72697479456E61626C656401034Q00A400015Q0010162Q0100014Q00C43Q00017Q001C3Q00030D3Q0053656C6563746564526F636B73027Q004003053Q005469746C6503083Q005072696F7269747903073Q00436F6E74656E7403163Q0053656C65637420322B20726F636B732066697273742103083Q004475726174696F6E03063Q00697061697273030E3Q00526F636B5072696F726974696573026Q00F03F03053Q007461626C6503063Q00696E7365727403043Q00726F636B03013Q007003043Q00736F72742Q033Q003173742Q033Q00326E642Q033Q003372642Q033Q003474682Q033Q003574682Q033Q003674682Q033Q003774682Q033Q0038746803023Q00746803023Q003A20030D3Q005072696F726974794C6162656C03053Q007063612Q6C030F3Q004F726465722072657665727365642100644Q00A47Q0020545Q00012Q002E2Q015Q0026322Q01000C0001000200046D3Q000C00012Q00A4000100014Q005200023Q000300302Q00020003000400302Q00020005000600302Q0002000700024Q0001000200012Q00C43Q00014Q004600016Q009900025Q00122Q000300086Q00048Q00030002000500044Q001C00012Q00A400085Q0020540008000800092Q00A6000800080007000640010800190001000100046D3Q001900012Q00D500080002000600203400080008000A2Q00D500090002000800203400090009000A2Q003F000100070009000677010300120001000200046D3Q001200012Q00A400035Q0010BF0003000900014Q00035Q00122Q000400086Q00058Q00040002000600044Q002F000100126A0109000B3Q0020FC00090009000C4Q000A00036Q000B3Q000200102Q000B000D00084Q000C5Q00202Q000C000C00094Q000C000C000800102Q000B000E000C4Q0009000B0001000677010400250001000200046D3Q0025000100126A0104000B3Q00205400040004000F2Q003C000500033Q0002BC00066Q00860004000600014Q00048Q000500083Q00122Q000600103Q00122Q000700113Q00122Q000800123Q00122Q000900133Q00122Q000A00143Q00122Q000B00153Q00122Q000C00163Q00122Q000D00176Q00050008000100126A010600084Q003C000700034Q006400060002000800046D3Q0052000100126A010B000B3Q002054000B000B000C2Q003C000C00044Q00A6000D00050009000640010D004E0001000100046D3Q004E00012Q003C000D00093Q001225010E00184Q007A000D000D000E001225010E00193Q002054000F000A000D2Q007A000D000D000F2Q007D000B000D0001000677010600450001000200046D3Q004500012Q00A4000600023Q00205400060006001A0006B40006005D00013Q00046D3Q005D000100126A0106001B3Q00066B01070001000100022Q00A43Q00024Q003C3Q00044Q009A0106000200012Q00A4000600014Q005200073Q000300302Q00070003000400302Q00070005001C00302Q0007000700024Q0006000200012Q00C43Q00013Q00023Q00013Q0003013Q007002083Q00205400023Q00010020540003000100010006D4000300050001000200046D3Q000500012Q001301026Q0012010200014Q003A000200024Q00C43Q00017Q00063Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403013Q002003053Q007461626C6503063Q00636F6E63617403023Q002Q20000C4Q00D07Q00206Q000100206Q000200122Q000200033Q00122Q000300043Q00202Q0003000300054Q000400013Q00122Q000500066Q0003000500024Q0002000200036Q000200016Q00017Q00013Q0003143Q005072696F726974795363616E496E74657276616C01034Q00A400015Q0010162Q0100014Q00C43Q00017Q00013Q0003163Q005072696F72697479537769746368432Q6F6C646F776E01034Q00A400015Q0010162Q0100014Q00C43Q00017Q00013Q0003113Q005072696F726974794477652Q6C54696D6501034Q00A400015Q0010162Q0100014Q00C43Q00017Q00013Q0003143Q005072696F72697479536B6970432Q6F6C646F776E01034Q00A400015Q0010162Q0100014Q00C43Q00017Q000B3Q00030E3Q00526F636B5072696F726974696573030D3Q005072696F726974794C6162656C03053Q007063612Q6C030B3Q0043752Q72656E74526F636B0003053Q005469746C6503083Q005072696F7269747903073Q00436F6E74656E7403123Q005072696F72697469657320636C656172656403083Q004475726174696F6E027Q004000144Q00C29Q0000015Q00104Q000100016Q00013Q00206Q000200064Q000B00013Q00046D3Q000B000100126A012Q00033Q00066B2Q013Q000100012Q00A43Q00014Q009A012Q000200012Q00A43Q00023Q0030243Q000400056Q00036Q00013Q000300302Q00010006000700302Q00010008000900302Q0001000A000B6Q000200016Q00013Q00013Q00033Q00030D3Q005072696F726974794C6162656C2Q033Q0053657403123Q005072696F72697469657320636C656172656400064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00103Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7303063Q006970616972732Q0103053Q007461626C6503063Q00696E73657274030C3Q0053656C65637465644F726573030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F74696669656403083Q004F72654C6162656C028Q0003063Q00636F6E63617403023Q002C20030F3Q00286E6F6E652073656C65637465642903053Q007063612Q6C01484Q003C00016Q00A400025Q0020540002000200010006B40002001D00013Q00046D3Q001D00012Q004600025Q00126A010300024Q00A4000400014Q006400030002000500046D3Q000B00010020090002000700030006770103000A0001000200046D3Q000A00012Q004600035Q00126A010400024Q003C00056Q006400040002000600046D3Q001A00012Q00A60009000200080006B40009001A00013Q00046D3Q001A000100126A010900043Q0020540009000900052Q003C000A00034Q003C000B00084Q007D0009000B0001000677010400120001000200046D3Q001200012Q003C000100034Q00A400025Q0010220002000600014Q000200023Q00302Q0002000700084Q000200026Q00035Q00102Q0002000900034Q000200026Q00035Q00102Q0002000A00034Q000200026Q00035Q00102Q0002000900034Q000200026Q00035Q00102Q0002000A00034Q000200033Q00202Q00020002000B00062Q0002004500013Q00046D3Q004500012Q00A400025Q0020540002000200062Q002E010200023Q000EA8010C003E0001000200046D3Q003E000100126A010200043Q00202700020002000D4Q00035Q00202Q00030003000600122Q0004000E6Q00020004000200062Q0002003F0001000100046D3Q003F00010012250102000F3Q00126A010300103Q00066B01043Q000100022Q00A43Q00034Q003C3Q00024Q009A0103000200012Q001D00026Q00A4000200044Q008C0002000100012Q00C43Q00013Q00013Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403183Q00476C6F62616C204F726573202866612Q6C6261636B293A2000084Q009F7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q000E3Q00030C3Q0053656C65637465644F726573030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F746966696564030B3Q004F726544726F70646F776E03053Q007063612Q6C03083Q004F72654C6162656C03053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403133Q00476C6F62616C206F72657320636C656172656403083Q004475726174696F6E027Q004000244Q00A48Q004600015Q001016012Q000100012Q00A43Q00013Q00300D3Q000200032Q00A43Q00014Q004600015Q001016012Q000400012Q00C23Q00016Q00015Q00104Q000500016Q00023Q00206Q000600064Q001300013Q00046D3Q0013000100126A012Q00073Q00066B2Q013Q000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q00080006B43Q001B00013Q00046D3Q001B000100126A012Q00073Q00066B2Q010001000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00034Q008C3Q000100012Q00A43Q00044Q005200013Q000300302Q00010009000A00302Q0001000B000C00302Q0001000D000E6Q000200012Q00C43Q00013Q00023Q00023Q00030B3Q004F726544726F70646F776E2Q033Q0053657400064Q00267Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403273Q00476C6F62616C204F726573202866612Q6C6261636B293A20286E6F6E652073656C65637465642900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00053Q0003113Q00557365476C6F62616C46612Q6C6261636B030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F746966696564010D4Q00A400015Q0010162Q0100014Q00A4000100013Q00300D0001000200032Q00A4000100014Q004600025Q0010162Q01000400022Q00A4000100014Q004600025Q0010162Q01000500022Q00A4000100024Q008C0001000100012Q00C43Q00017Q00013Q0003193Q004175746F5472696D496E76616C696453656C656374696F6E7301034Q00A400015Q0010162Q0100014Q00C43Q00017Q00063Q00028Q0003143Q00284E6F20726F636B7320617661696C61626C652903063Q00286E6F6E652903063Q0069706169727303053Q007461626C6503063Q00696E73657274001A4Q00A48Q002E016Q000EA82Q01000700013Q00046D3Q000700012Q00A47Q000640012Q000A0001000100046D3Q000A00012Q00463Q00013Q0012252Q0100024Q00CD3Q000100012Q0046000100013Q001225010200034Q00CD00010001000100126A010200044Q003C00036Q006400020002000400046D3Q0016000100126A010700053Q0020540007000700062Q003C000800014Q003C000900064Q007D000700090001000677010200110001000200046D3Q001100012Q003A000100024Q00C43Q00017Q00063Q00028Q0003133Q002853656C65637420617265612066697273742903063Q00286E6F6E652903063Q0069706169727303053Q007461626C6503063Q00696E73657274001A4Q00A48Q002E016Q000EA82Q01000700013Q00046D3Q000700012Q00A47Q000640012Q000A0001000100046D3Q000A00012Q00463Q00013Q0012252Q0100024Q00CD3Q000100012Q0046000100013Q001225010200034Q00CD00010001000100126A010200044Q003C00036Q006400020002000400046D3Q0016000100126A010700053Q0020540007000700062Q003C000800014Q003C000900064Q007D000700090001000677010200110001000200046D3Q001100012Q003A000100024Q00C43Q00017Q00103Q00026Q00F03F026Q000840030A3Q0046696C746572536C6F7403053Q004C6162656C030E3Q00526F636B4F726546696C7465727303043Q00526F636B03043Q004F726573028Q0003053Q007461626C6503063Q00636F6E63617403023Q002C20026Q003E402Q033Q00737562026Q003B402Q033Q003Q2E03053Q007063612Q6C00483Q001225012Q00013Q0012252Q0100023Q001225010200013Q0004B13Q004700012Q00A400045Q00129B010500036Q000600033Q00122Q000700046Q0005000500074Q00040004000500062Q0004004500013Q00046D3Q004500012Q00A4000500013Q0020540005000500050006B40005001300013Q00046D3Q001300012Q00A4000500013Q0020540005000500052Q00A60005000500030006B40005003500013Q00046D3Q003500010020540006000500060006B40006003500013Q00046D3Q003500010020540006000500070006B40006003500013Q00046D3Q003500010020540006000500072Q002E010600063Q000EA8010800350001000600046D3Q0035000100126A010600093Q00201101060006000A00202Q00070005000700122Q0008000B6Q0006000800024Q000700063Q000E2Q000C002D0001000700046D3Q002D000100203800070006000D001225010900013Q001225010A000E4Q004C0007000A00020012250108000F4Q007A00060007000800126A010700103Q00066B01083Q000100032Q003C3Q00044Q003C3Q00054Q003C3Q00064Q009A0107000200012Q001D00065Q00046D3Q004400010006B40005004000013Q00046D3Q004000010020540006000500060006B40006004000013Q00046D3Q0040000100126A010600103Q00066B01070001000100022Q003C3Q00044Q003C3Q00054Q009A01060002000100046D3Q0044000100126A010600103Q00066B01070002000100012Q003C3Q00044Q009A0106000200012Q001D00056Q001D00045Q00041C012Q000400012Q00C43Q00013Q00033Q00043Q002Q033Q0053657403043Q00E286922003043Q00526F636B03023Q003A20000A4Q009D7Q00206Q000100122Q000200026Q000300013Q00202Q00030003000300122Q000400046Q000500026Q0002000200056Q000200016Q00017Q00043Q002Q033Q0053657403043Q00E286922003043Q00526F636B030B3Q003A20286E6F206F7265732900094Q00A47Q0020385Q0001001225010200024Q00A4000300013Q002054000300030003001225010400044Q007A0002000200042Q007D3Q000200012Q00C43Q00017Q00023Q002Q033Q00536574030B3Q00E286922028656D7074792900054Q0042016Q00206Q000100122Q000200028Q000200016Q00019Q002Q0001093Q00066B2Q013Q000100062Q00A48Q003C8Q00A43Q00014Q00A43Q00024Q00A43Q00034Q00A43Q00044Q003A000100024Q00C43Q00013Q00013Q00083Q0003043Q007479706503053Q007461626C65026Q00F03F03063Q00286E6F6E6529030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F74696669656401213Q00126A2Q0100014Q003C00026Q00B8000100020002002680000100080001000200046D3Q0008000100205400013Q00030006402Q0100090001000100046D3Q000900012Q003C00015Q0026800001000C0001000400046D3Q000C00012Q002C000100014Q00A400026Q001F010300016Q0002000200034Q000400026Q000500016Q000600016Q000700036Q0004000700014Q000400033Q00302Q0004000500064Q000400034Q004600055Q0010160104000700052Q00A4000400034Q004600055Q0010160104000800052Q00A4000400044Q008C0004000100012Q00A4000400054Q008C0004000100012Q00C43Q00019Q002Q0001093Q00066B2Q013Q000100062Q00A48Q003C8Q00A43Q00014Q00A43Q00024Q00A43Q00034Q00A43Q00044Q003A000100024Q00C43Q00013Q00013Q000A3Q0003043Q007479706503053Q007461626C6503063Q0069706169727303063Q00286E6F6E6529034Q0003063Q00696E73657274030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F74696669656401313Q00126A2Q0100014Q003C00026Q00B8000100020002002680000100070001000200046D3Q000700010006392Q01000A00013Q00046D3Q000A00012Q0046000100014Q003C00026Q00CD0001000100012Q004600025Q00126A010300034Q003C000400014Q006400030002000500046D3Q001A00010006B40007001A00013Q00046D3Q001A00010026A70107001A0001000400046D3Q001A00010026A70107001A0001000500046D3Q001A000100126A010800023Q0020540008000800062Q003C000900024Q003C000A00074Q007D0008000A00010006770103000F0001000200046D3Q000F00012Q00A400036Q001F010400016Q0003000200044Q000500026Q000600016Q000700036Q000800026Q0005000800014Q000500033Q00302Q0005000700084Q000500034Q004600065Q0010160105000900062Q00A4000500034Q004600065Q0010160105000A00062Q00A4000500044Q008C0005000100012Q00A4000500054Q008C0005000100012Q00C43Q00017Q00103Q00026Q00F03F026Q000840030A3Q0046696C746572536C6F7403043Q00526F636B2Q033Q004F726503053Q007063612Q6C030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F74696669656403053Q005469746C6503063Q004D696E696E6703073Q00436F6E74656E7403183Q00412Q6C20736C6F742066696C7465727320636C656172656403083Q004475726174696F6E027Q004000363Q001225012Q00013Q0012252Q0100023Q001225010200013Q0004B13Q002300012Q00A400046Q0069000500036Q000600066Q00078Q0004000700014Q000400013Q00122Q000500036Q000600033Q00122Q000700046Q0005000500074Q0004000400052Q00A4000500013Q00129B010600036Q000700033Q00122Q000800056Q0006000600084Q00050005000600062Q0004001B00013Q00046D3Q001B000100126A010600063Q00066B01073Q000100012Q003C3Q00044Q009A0106000200010006B40005002100013Q00046D3Q0021000100126A010600063Q00066B01070001000100012Q003C3Q00054Q009A0106000200012Q001D00045Q00041C012Q000400012Q00A43Q00023Q003078012Q000700086Q00026Q00015Q00104Q000900016Q00026Q00015Q00104Q000A00016Q00038Q000100016Q00044Q008C3Q000100012Q00A43Q00054Q005200013Q000300302Q0001000B000C00302Q0001000D000E00302Q0001000F00106Q000200012Q00C43Q00013Q00023Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q001E016Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q007D3Q000200012Q00C43Q00017Q00023Q002Q033Q0053657403063Q00286E6F6E652900074Q001E016Q00206Q00014Q000200013Q00122Q000300026Q0002000100012Q007D3Q000200012Q00C43Q00017Q001F3Q00026Q00F03F03093Q0048656176656E697465027Q0040030A3Q0047617267616E7475616E03083Q00537572796166616C030B3Q00457468657265616C697465026Q00084003063Q00286E6F6E6529030A3Q0046696C746572536C6F742Q033Q004F726503053Q007063612Q6C03053Q007461626C6503063Q00696E7365727403083Q00746F737472696E67028Q0003053Q005469746C65030E3Q00536C6F742054656D706C6174657303073Q00436F6E74656E7403173Q005069636B20726F636B20666F7220736C6F742873293A2003063Q00636F6E63617403023Q002C2003083Q004475726174696F6E030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F74696669656403123Q00412Q706C69656420746F20736C6F74733A2003193Q004D692Q73696E6720726F636B20696E20736C6F742873293A2003163Q00536C6F742054656D706C6174657320412Q706C69656403013Q000A026Q00104000854Q003F019Q000100018Q000200018Q00034Q000100013Q00122Q000200026Q000100010001001016012Q000100012Q0046000100033Q001225010200043Q001225010300053Q001225010400064Q00CD000100030001001016012Q000300012Q0046000100023Q001225010200043Q001225010300054Q00CD000100020001001016012Q000700012Q00262Q018Q00025Q00122Q000300013Q00122Q000400073Q00122Q000500013Q00042Q0003004500012Q00A4000700014Q003C000800064Q00640007000200080006B40007003C00013Q00046D3Q003C00010026A70107003C0001000800046D3Q003C00012Q00A4000900024Q0073000A00066Q000B00076Q000C3Q00064Q0009000C00014Q000900033Q00129B010A00096Q000B00063Q00122Q000C000A6Q000A000A000C4Q00090009000A00062Q0009003300013Q00046D3Q0033000100126A010A000B3Q00066B010B3Q000100032Q003C3Q00094Q003C8Q003C3Q00064Q009A010A0002000100126A010A000C3Q002055000A000A000D4Q000B00013Q00122Q000C000E6Q000D00066Q000C000D6Q000A3Q00014Q00095Q00044Q0043000100126A0109000C3Q0020F100090009000D4Q000A00023Q00122Q000B000E6Q000C00066Q000B000C6Q00093Q00012Q001D00065Q00041C0103001900012Q002E010300013Q002680000300560001000F00046D3Q005600012Q00A4000300044Q004600043Q000300300D000400100011001225010500133Q00126A0106000C3Q0020540006000600142Q003C000700023Q001225010800154Q004C0006000800022Q007A00050005000600101601040012000500300D0004001600072Q009A0103000200012Q00C43Q00014Q00A4000300053Q00302F0003001700184Q000300056Q00045Q00102Q0003001900044Q000300056Q00045Q00102Q0003001A00044Q000300066Q0003000100014Q000300076Q0003000100014Q000300013Q00122Q0004001B3Q00122Q0005000C3Q00202Q0005000500144Q000600013Q00122Q000700156Q0005000700024Q0004000400054Q0003000100012Q002E010400023Q000EA8010F00790001000400046D3Q0079000100126A0104000C3Q0020FD00040004000D4Q000500033Q00122Q0006001C3Q00122Q0007000C3Q00202Q0007000700144Q000800023Q00122Q000900156Q0007000900024Q0006000600074Q0004000600012Q00A4000400044Q00DB00053Q000300302Q00050010001D00122Q0006000C3Q00202Q0006000600144Q000700033Q00122Q0008001E6Q00060008000200102Q00050012000600302Q00050016001F4Q0004000200016Q00013Q00013Q00013Q002Q033Q0053657400074Q00A47Q0020385Q00012Q00A4000200014Q00A4000300024Q00A60002000200032Q007D3Q000200012Q00C43Q00017Q001F3Q0003043Q007479706503053Q007461626C65026Q00F03F028Q0003063Q006970616972732Q0103063Q00696E7365727403193Q004175746F5472696D496E76616C696453656C656374696F6E7303053Q005469746C65030D3Q004F72652054656D706C6174657303073Q00436F6E74656E7403283Q004F7265206C697374206E6F742072656164793B20612Q706C69656420776974686F7574207472696D03083Q004475726174696F6E026Q000840030C3Q0053656C65637465644F726573030B3Q004F726544726F70646F776E03053Q007063612Q6C03083Q004F72654C6162656C03063Q00636F6E63617403023Q002C20030F3Q00286E6F6E652073656C656374656429030B3Q0043752Q72656E74526F636B00030C3Q00536B692Q706564526F636B73030F3Q004F7265536B69704E6F74696669656403063Q00286E6F6E652903193Q0054656D706C61746520412Q706C6965642028476C6F62616C2903013Q000A03053Q007072696E74032F3Q005B466F726765204D696E696E675D204F72652054656D706C61746520412Q706C69656420746F20474C4F42414C3A2003093Q00207C204F7265733A2001983Q00126A2Q0100014Q003C00026Q00B8000100020002002680000100080001000200046D3Q0008000100205400013Q00030006402Q0100090001000100046D3Q000900012Q003C00015Q0006B40001000F00013Q00046D3Q000F00012Q00A400026Q00A6000200020001000640010200100001000100046D3Q001000012Q00C43Q00014Q00A400026Q00DD0002000200014Q000300016Q000400016Q0003000200014Q000300026Q000300033Q000E2Q0004001A0001000300046D3Q001A00012Q001301036Q0012010300014Q004600045Q0006B40003002500013Q00046D3Q0025000100126A010500054Q00A4000600024Q006400050002000700046D3Q00230001002009000400090006000677010500220001000200046D3Q002200012Q004600055Q0006B40003003600013Q00046D3Q0036000100126A010600054Q003C000700024Q006400060002000800046D3Q003400012Q00A6000B0004000A0006B4000B003400013Q00046D3Q0034000100126A010B00023Q002054000B000B00072Q003C000C00054Q003C000D000A4Q007D000B000D00010006770106002C0001000200046D3Q002C00012Q003C000600024Q00A4000700033Q0020540007000700080006B40007003F00013Q00046D3Q003F00010006B40003003F00013Q00046D3Q003F00012Q003C000600053Q00046D3Q004B00012Q00A4000700033Q0020540007000700080006B40007004B00013Q00046D3Q004B00010006400103004B0001000100046D3Q004B00012Q00A4000700044Q005200083Q000300302Q00080009000A00302Q0008000B000C00302Q0008000D000E4Q0007000200012Q00A4000700033Q0010160107000F00062Q00A4000700053Q0020540007000700100006B40007005600013Q00046D3Q0056000100126A010700113Q00066B01083Q000100022Q00A43Q00054Q00A43Q00034Q009A0107000200012Q00A4000700053Q0020540007000700120006B40007006E00013Q00046D3Q006E00012Q00A4000700033Q00205400070007000F2Q002E010700073Q000EA8010400670001000700046D3Q0067000100126A010700023Q0020270007000700134Q000800033Q00202Q00080008000F00122Q000900146Q00070009000200062Q000700680001000100046D3Q00680001001225010700153Q00126A010800113Q00066B01090001000100022Q00A43Q00054Q003C3Q00074Q009A0108000200012Q001D00076Q00A4000700063Q0030780107001600174Q000700066Q00085Q00102Q0007001800084Q000700066Q00085Q00102Q0007001900084Q000700076Q0007000100014Q000700033Q00205400070007000F2Q002E010700073Q000EA8010400850001000700046D3Q0085000100126A010700023Q0020270007000700134Q000800033Q00202Q00080008000F00122Q000900146Q00070009000200062Q000700860001000100046D3Q008600010012250107001A4Q00A4000800044Q007000093Q000300302Q00090009001B4Q000A00013Q00122Q000B001C6Q000C00076Q000A000A000C00102Q0009000B000A00302Q0009000D000E4Q00080002000100122Q0008001D3Q00122Q0009001E6Q000A00013Q00122Q000B001F6Q000C00076Q00090009000C4Q0008000200016Q00013Q00023Q00033Q00030B3Q004F726544726F70646F776E2Q033Q00536574030C3Q0053656C65637465644F72657300074Q0050016Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403183Q00476C6F62616C204F726573202866612Q6C6261636B293A2000084Q009F7Q00206Q000100206Q000200122Q000200036Q000300016Q0002000200036Q000200016Q00017Q00013Q00030F3Q004F7265436865636B456E61626C656401034Q00A400015Q0010162Q0100014Q00C43Q00017Q00013Q00030D3Q004F7265536B69704E6F7469667901034Q00A400015Q0010162Q0100014Q00C43Q00017Q00033Q0003143Q00412Q6C6F774F726546696C746572427970612Q7303153Q0049676E6F72654F726546696C74657273556E74696C028Q0001074Q00A400015Q0010162Q0100013Q000640012Q00060001000100046D3Q000600012Q00A4000100013Q00300D0001000200032Q00C43Q00017Q00393Q00030A3Q004175746F4D696E696E67010003103Q004175746F4D696E696E67546F2Q676C6503053Q007063612Q6C03053Q00706169727303043Q007479706503053Q007461626C65030E3Q00526F636B4F726546696C7465727303103Q004C61737446696C746572536F7572636500030E3Q004C61737446696C746572526F636B030D3Q004E6F54617267657453696E636503153Q0049676E6F72654F726546696C74657273556E74696C028Q00030B3Q0043752Q72656E74526F636B030C3Q0043752Q72656E745068617365030A3Q00536B69704672616D6573030E3Q00536B69704D696E654672616D6573030D3Q004C6F636B65644D696E65506F73030A3Q00546F74616C4D696E656403103Q004D61696E74656E616E6365436F756E74030E3Q004C6173744C2Q6F6B546172676574030E3Q004C617374526F636B536561726368030D3Q004C6173744E6F526F636B4C6F67030D3Q004C617374536B69705265736574030C3Q00536B692Q706564526F636B7303113Q004C6173744F7265536B69704E6F74696679030F3Q004F7265536B69704E6F74696669656403153Q004C617374416C72656164794D696E696E6754696D65030D3Q0050656E64696E6753776974636803113Q004C61737450656E64696E67537769746368030A3Q004C617374526F636B4850030B3Q004C617374526F636B52656603123Q004D696E657353696E636548504368616E6765030E3Q00537475636B436865636B54696D65030D3Q005265636F766572794C6576656C03103Q004C6173745265636F7665727954696D65030E3Q004C32412Q74656D7074436F756E74030B3Q004465627567546F2Q676C65030E3Q004F7265436865636B546F2Q676C6503133Q004F7265536B69704E6F74696679546F2Q676C6503153Q004F726546696C746572427970612Q73546F2Q676C6503173Q00557365476C6F62616C46612Q6C6261636B546F2Q676C65030B3Q004F726544726F70646F776E03083Q004F72654C6162656C03113Q0041637469766546696C7465724C6162656C030E3Q0046696C746572536C6F74314F7265030E3Q0046696C746572536C6F74324F7265030E3Q0046696C746572536C6F74334F726503123Q00526F636B4F726546696C7465724C6162656C03133Q00416374697665526F636B4F726546696C74657203073Q0044657374726F7903023Q005F4703053Q00466F726765030D3Q0052657365744D696E696E67554903053Q007072696E7403223Q005B466F726765204D696E696E675D2046752Q6C20526573657420436F6D706C65746500DD4Q00427Q00304Q000100026Q00018Q000100016Q00023Q00206Q000300064Q000C00013Q00046D3Q000C000100126A012Q00043Q00066B2Q013Q000100012Q00A43Q00024Q009A012Q0002000100126A012Q00054Q00A4000100034Q00643Q0002000200046D3Q0024000100126A010500064Q003C000600044Q00B8000500020002002680000500220001000700046D3Q002200012Q00A400056Q003D01068Q00050003000600122Q000500056Q000600046Q00050002000700044Q001F00012Q00A4000A6Q00A6000A000A00032Q003F000A000800090006770105001C0001000200046D3Q001C000100046D3Q002400012Q00A400056Q003F000500030004000677012Q00100001000200046D3Q001000012Q00A48Q004600015Q001016012Q000800012Q0049012Q00043Q00304Q0009000A6Q00043Q00304Q000B000A6Q00043Q00304Q000C000A6Q00043Q00304Q000D000E6Q00043Q00304Q000F000A2Q0049012Q00043Q00304Q0010000E6Q00043Q00304Q0011000E6Q00043Q00304Q0012000E6Q00043Q00304Q0013000A6Q00043Q00304Q0014000E2Q0049012Q00043Q00304Q0015000E6Q00043Q00304Q0016000A6Q00043Q00304Q0017000A6Q00043Q00304Q0018000A6Q00043Q00304Q0019000E2Q00A43Q00044Q00352Q015Q00104Q001A00016Q00043Q00304Q001B000E6Q00046Q00015Q00104Q001C00016Q00043Q00304Q001D000E6Q00043Q0030313Q001E00026Q00043Q00304Q001F000E6Q00043Q00304Q0020000A6Q00043Q00304Q0021000A6Q00043Q00304Q0022000E6Q00043Q00300D3Q0023000E2Q00A43Q00043Q0030133Q0024000E6Q00043Q00304Q0025000E6Q00043Q00304Q0026000E6Q00023Q00206Q002700064Q006B00013Q00046D3Q006B000100126A012Q00043Q00066B2Q010001000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q00280006B43Q007400013Q00046D3Q0074000100126A012Q00043Q00066B2Q010002000100022Q00A43Q00024Q00A43Q00034Q009A012Q000200012Q00A43Q00023Q0020545Q00290006B43Q007D00013Q00046D3Q007D000100126A012Q00043Q00066B2Q010003000100022Q00A43Q00024Q00A43Q00034Q009A012Q000200012Q00A43Q00023Q0020545Q002A0006B43Q008600013Q00046D3Q0086000100126A012Q00043Q00066B2Q010004000100022Q00A43Q00024Q00A43Q00034Q009A012Q000200012Q00A43Q00023Q0020545Q002B0006B43Q008F00013Q00046D3Q008F000100126A012Q00043Q00066B2Q010005000100022Q00A43Q00024Q00A43Q00034Q009A012Q000200012Q00A43Q00023Q0020545Q002C0006B43Q009700013Q00046D3Q0097000100126A012Q00043Q00066B2Q010006000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q002D0006B43Q009F00013Q00046D3Q009F000100126A012Q00043Q00066B2Q010007000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q002E0006B43Q00A700013Q00046D3Q00A7000100126A012Q00043Q00066B2Q010008000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q002F0006B43Q00AF00013Q00046D3Q00AF000100126A012Q00043Q00066B2Q010009000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q00300006B43Q00B700013Q00046D3Q00B7000100126A012Q00043Q00066B2Q01000A000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q00310006B43Q00BF00013Q00046D3Q00BF000100126A012Q00043Q00066B2Q01000B000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q0020545Q00320006B43Q00C700013Q00046D3Q00C7000100126A012Q00043Q00066B2Q01000C000100012Q00A43Q00024Q009A012Q000200012Q00A43Q00023Q00300D3Q0033000A2Q00A43Q00053Q0006B43Q00D100013Q00046D3Q00D100012Q00A43Q00053Q0020385Q00342Q009A012Q000200012Q002C8Q00D73Q00053Q00126A012Q00353Q0020545Q00360020545Q00370006B43Q00D900013Q00046D3Q00D9000100126A012Q00043Q0002BC0001000D4Q009A012Q0002000100126A012Q00383Q0012252Q0100394Q009A012Q000200012Q00C43Q00013Q000E3Q00023Q0003103Q004175746F4D696E696E67546F2Q676C652Q033Q0053657400064Q00DE7Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00023Q00030B3Q004465627567546F2Q676C652Q033Q0053657400064Q00DE7Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q00030E3Q004F7265436865636B546F2Q676C652Q033Q00536574030F3Q004F7265436865636B456E61626C656400074Q0050016Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003133Q004F7265536B69704E6F74696679546F2Q676C652Q033Q00536574030D3Q004F7265536B69704E6F7469667900074Q0050016Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003153Q004F726546696C746572427970612Q73546F2Q676C652Q033Q0053657403143Q00412Q6C6F774F726546696C746572427970612Q7300074Q0050016Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00033Q0003173Q00557365476C6F62616C46612Q6C6261636B546F2Q676C652Q033Q0053657403113Q00557365476C6F62616C46612Q6C6261636B00074Q0050016Q00206Q000100206Q00024Q000200013Q00202Q0002000200036Q000200016Q00017Q00023Q00030B3Q004F726544726F70646F776E2Q033Q0053657400064Q00267Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00033Q0003083Q004F72654C6162656C2Q033Q0053657403273Q00476C6F62616C204F726573202866612Q6C6261636B293A20286E6F6E652073656C65637465642900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003113Q0041637469766546696C7465724C6162656C2Q033Q0053657403133Q004163746976652046696C7465723A204E6F6E6500064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q00030E3Q0046696C746572536C6F74314F72652Q033Q0053657403063Q00286E6F6E652900084Q0099016Q00206Q000100206Q00024Q000200013Q00122Q000300036Q0002000100012Q007D3Q000200012Q00C43Q00017Q00033Q00030E3Q0046696C746572536C6F74324F72652Q033Q0053657403063Q00286E6F6E652900084Q0099016Q00206Q000100206Q00024Q000200013Q00122Q000300036Q0002000100012Q007D3Q000200012Q00C43Q00017Q00033Q00030E3Q0046696C746572536C6F74334F72652Q033Q0053657403063Q00286E6F6E652900084Q0099016Q00206Q000100206Q00024Q000200013Q00122Q000300036Q0002000100012Q007D3Q000200012Q00C43Q00017Q00033Q0003123Q00526F636B4F726546696C7465724C6162656C2Q033Q00536574030B3Q00287069636B20726F636B2900064Q005C016Q00206Q000100206Q000200122Q000200038Q000200016Q00017Q00033Q0003023Q005F4703053Q00466F726765030D3Q0052657365744D696E696E67554900053Q00127D012Q00013Q00206Q000200206Q00036Q000100016Q00017Q00043Q00030A3Q004175746F4D696E696E67010003103Q004175746F4D696E696E67546F2Q676C6503053Q007063612Q6C00194Q00A47Q0020545Q0001000640012Q000A0001000100046D3Q000A00012Q00A43Q00014Q00A4000100024Q00B83Q00020002000640012Q000A0001000100046D3Q000A00012Q00C43Q00014Q00A47Q0030A03Q000100026Q00038Q000100016Q00048Q000100016Q00053Q00206Q000300064Q001800013Q00046D3Q0018000100126A012Q00043Q00066B2Q013Q000100012Q00A43Q00054Q009A012Q000200012Q00C43Q00013Q00013Q00023Q0003103Q004175746F4D696E696E67546F2Q676C652Q033Q0053657400064Q00DE7Q00206Q000100206Q00024Q00029Q00000200016Q00017Q00", GetFEnv(), ...);
